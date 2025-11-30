#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"

#include <vector>
#include <string>
#include <cstring>  // for strcmp

// ----------------------------------------------------------------------
//  forward declaration from dar (照題目 hint 2)
// ----------------------------------------------------------------------
extern "C" {
Aig_Man_t* Abc_NtkToDar(Abc_Ntk_t* pNtk, int fExors, int fRegisters);
}

// 把 SAT 變數 v 和 value(0/1) 轉成 literal
//   value = 1 -> v
//   value = 0 -> !v
static inline lit LitOf(int var, int value) {
    return toLitCond(var, value ? 0 : 1);
}

// 從 SAT model 讀出一個 pattern：
//
//  - pattern 長度 = 原網路的 nPis
//  - 第 piIndex 個位置輸出 '-'
//  - 其餘：
//      * 如果該 PI 有在 cone 裡 (對應 SAT var >= 0)，就讀 SAT model
//      * 否則當作 don't care，這裡輸出 '0'
static std::string BuildPatternFromModel(
    sat_solver*  pSat,
    Vec_Int_t*   vPiVarsByOrig,   // index = 原網路 PI index, 內容 = SAT var 或 -1
    int          piIndex,         // 原網路的 i
    int          nPis             // 原網路 PI 數
) {
    std::string pat;
    pat.reserve(nPis);

    for (int t = 0; t < nPis; ++t) {
        if (t == piIndex) {
            pat.push_back('-');
            continue;
        }

        int var = Vec_IntEntry(vPiVarsByOrig, t);
        int val = 0;
        if (var >= 0)
            val = sat_solver_var_value(pSat, var);

        pat.push_back(val ? '1' : '0');
    }
    return pat;
}

// ----------------------------------------------------------------------
//  Q2: lsv_unate_sat <k> <i>
// ----------------------------------------------------------------------
int Lsv_CommandUnateSat(Abc_Frame_t* pAbc, int argc, char** argv)
{
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_sat <k> <i>\n");
        Abc_Print(-1, "  k : 0-based primary output index\n");
        Abc_Print(-1, "  i : 0-based primary input index\n");
        return 1;
    }

    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    if (!Abc_NtkIsStrash(pNtk)) {
        Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
        return 1;
    }

    if (!Abc_NtkIsComb(pNtk)) {
        Abc_Print(-1, "The network is not combinational. Run \"comb\" first.\n");
        return 1;
    }

    int k = atoi(argv[1]);
    int i = atoi(argv[2]);

    int nPos = Abc_NtkPoNum(pNtk);
    int nPis = Abc_NtkPiNum(pNtk);

    if (k < 0 || k >= nPos) {
        Abc_Print(-1, "Output index k (%d) is out of range [0, %d).\n", k, nPos);
        return 1;
    }
    if (i < 0 || i >= nPis) {
        Abc_Print(-1, "Input index i (%d) is out of range [0, %d).\n", i, nPis);
        return 1;
    }

    Abc_Print(-1, "SAT Debug: k=%d, i=%d, nPOs=%d, nPIs=%d\n", k, i, nPos, nPis);

    // --- debug: 印原網路的 PI 資訊 ---
    Abc_Print(-1, "SAT Debug: Original network PIs:\n");
    {
        Abc_Obj_t* pPiOrigObj;
        int idxOrig;
        Abc_NtkForEachPi(pNtk, pPiOrigObj, idxOrig) {
            Abc_Print(-1, "  Orig PI[%d]: Id=%d, Name=%s\n",
                      idxOrig, Abc_ObjId(pPiOrigObj), Abc_ObjName(pPiOrigObj));
        }
    }

    // 要手動 free 的資源
    Abc_Ntk_t*  pCone = nullptr;
    Aig_Man_t*  pAig  = nullptr;
    sat_solver* pSat  = nullptr;
    Cnf_Dat_t*  pCnfA = nullptr;
    Cnf_Dat_t*  pCnfB = nullptr;
    Vec_Int_t*  vPiA  = nullptr;   // 長度 = nPis, index = 原網路 PI index, value = SAT var (A copy)
    Vec_Int_t*  vPiB  = nullptr;   // 同上, B copy

    auto cleanup = [&]() {
        if (vPiA)  { Vec_IntFree(vPiA);  vPiA  = nullptr; }
        if (vPiB)  { Vec_IntFree(vPiB);  vPiB  = nullptr; }
        if (pCnfA) { Cnf_DataFree(pCnfA); pCnfA = nullptr; }
        if (pCnfB) { Cnf_DataFree(pCnfB); pCnfB = nullptr; }
        if (pSat)  { sat_solver_delete(pSat); pSat = nullptr; }
        if (pAig)  { Aig_ManStop(pAig);  pAig  = nullptr; }
        if (pCone) { Abc_NtkDelete(pCone); pCone = nullptr; }
    };

    // ---------------------------
    // 1) 建 cone：根用 k-th PO 的 fanin
    // ---------------------------
    Abc_Obj_t* pCoOrig   = Abc_NtkCo(pNtk, k);
    Abc_Obj_t* pRootNtk  = Abc_ObjFanin0(pCoOrig);

    // 第 4 個參數設 1，確保所有輸入都納入 cone（照 hint 3）
    pCone = Abc_NtkCreateCone(pNtk, pRootNtk, Abc_ObjName(pCoOrig), 1);
    if (!pCone) {
        Abc_Print(-1, "Abc_NtkCreateCone failed.\n");
        cleanup();
        return 1;
    }

    Abc_Print(-1, "SAT Debug: Cone PIs:\n");
    {
        Abc_Obj_t* pPiConeObj;
        int idxCone;
        Abc_NtkForEachPi(pCone, pPiConeObj, idxCone) {
            Abc_Print(-1, "  Cone PI[%d]: Id=%d, Name=%s\n",
                      idxCone, Abc_ObjId(pPiConeObj), Abc_ObjName(pPiConeObj));
        }
    }

    // === 建立「原網路 PI index -> cone PI index」的對應 (orig2cone) ===
    std::vector<int> orig2cone(nPis, -1);
    {
        Abc_Obj_t* pPiOrig;
        int idxOrig;
        Abc_NtkForEachPi(pNtk, pPiOrig, idxOrig) {
            Abc_Obj_t* pPiCone;
            int idxCone;
            Abc_NtkForEachPi(pCone, pPiCone, idxCone) {
                if (strcmp(Abc_ObjName(pPiOrig), Abc_ObjName(pPiCone)) == 0) {
                    orig2cone[idxOrig] = idxCone;
                    break;
                }
            }
        }

        Abc_Print(-1, "SAT Debug: orig2cone mapping (orig index -> cone index):\n");
        for (int t = 0; t < nPis; ++t) {
            Abc_Print(-1, "  orig %d -> cone %d\n", t, orig2cone[t]);
        }
    }

    int idxConeI = orig2cone[i];
    if (idxConeI < 0) {
        Abc_Print(-1, "PI %d is not in the cone of output %d.\n", i, k);
        cleanup();
        return 1;
    }

    // ---------------------------
    // 2) Cone -> AIG
    // ---------------------------
    pAig = Abc_NtkToDar(pCone, 0, 0);
    if (!pAig) {
        Abc_Print(-1, "Abc_NtkToDar failed.\n");
        cleanup();
        return 1;
    }

    // ---------------------------
    // 3) SAT solver
    // ---------------------------
    pSat = sat_solver_new();
    if (!pSat) {
        Abc_Print(-1, "sat_solver_new failed.\n");
        cleanup();
        return 1;
    }

    // ---------------------------
    // 4) CNF for copy A
    // ---------------------------
    pCnfA = Cnf_Derive(pAig, 1);
    if (!pCnfA) {
        Abc_Print(-1, "Cnf_Derive for C_A failed.\n");
        cleanup();
        return 1;
    }

    sat_solver_setnvars(pSat, pCnfA->nVars * 2);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfA, 1, 0);

    // ---------------------------
    // 5) CNF for copy B (lifted)
    // ---------------------------
    pCnfB = Cnf_Derive(pAig, 1);
    if (!pCnfB) {
        Abc_Print(-1, "Cnf_Derive for C_B failed.\n");
        cleanup();
        return 1;
    }

    Cnf_DataLift(pCnfB, pCnfA->nVars);
    Cnf_DataWriteIntoSolverInt(pSat, pCnfB, 1, 0);

    // ---------------------------
    // 6) 建立 vPiA / vPiB：index = 原網路 PI index
    // ---------------------------
    // vPiA / vPiB 長度 = 原網路的 nPis
    //   - Vec_IntEntry(vPiA, t) = 該原始 PI[t] 在 copy A 裡的 SAT var（或 -1 表示不在 cone）
    //   - Vec_IntEntry(vPiB, t) = 在 copy B 裡的 SAT var
    vPiA = Vec_IntStart(nPis);
    vPiB = Vec_IntStart(nPis);

    for (int origIdx = 0; origIdx < nPis; ++origIdx) {
        int coneIdx = orig2cone[origIdx];
        if (coneIdx < 0) {
            // 這個 PI 不在 cone 裡
            Vec_IntWriteEntry(vPiA, origIdx, -1);
            Vec_IntWriteEntry(vPiB, origIdx, -1);
            continue;
        }

        // cone 裡對應的那顆 PI
        Abc_Obj_t* pPiCone = Abc_NtkPi(pCone, coneIdx);

        // Abc_NtkToDar 之後，pPiCone->pCopy 指向 AIG 的 CI
        Aig_Obj_t* pCiAig = (Aig_Obj_t*)pPiCone->pCopy;
        if (!pCiAig) {
            Abc_Print(-1, "Error: pPiCone->pCopy is NULL for cone PI %d\n", coneIdx);
            cleanup();
            return 1;
        }

        // 這顆 CI 在 CNF A 裡的變數編號
        int varA = pCnfA->pVarNums[pCiAig->Id];
        // copy B 是用 Cnf_DataLift(pCnfB, pCnfA->nVars) 提升過
        int varB = varA + pCnfA->nVars;

        Vec_IntWriteEntry(vPiA, origIdx, varA);
        Vec_IntWriteEntry(vPiB, origIdx, varB);
    }

    Abc_Print(-1, "SAT Debug: PI var mapping (orig index -> varA, varB):\n");
    for (int t = 0; t < nPis; ++t) {
        Abc_Print(-1, "  PI %d: varA=%d, varB=%d\n",
                  t, Vec_IntEntry(vPiA, t), Vec_IntEntry(vPiB, t));
    }

    // 第 i 個「原網路 PI」對應的 SAT 變數
    int varXiA = Vec_IntEntry(vPiA, i);
    int varXiB = Vec_IntEntry(vPiB, i);
    if (varXiA < 0 || varXiB < 0) {
        Abc_Print(-1, "PI index i (%d) is not in the cone.\n", i);
        cleanup();
        return 1;
    }

    // ---------------------------
    // 7) 找「這個 cone 的唯一輸出 y_k」在 CNF 裡的 literal
    //    用 ABC 提供的 Cnf_DataCollectCoSatNums，比自己看 pVarNums 安全
    // ---------------------------
    Vec_Int_t* vCoA = Cnf_DataCollectCoSatNums(pCnfA, pAig);
    Vec_Int_t* vCoB = Cnf_DataCollectCoSatNums(pCnfB, pAig);
    if (!vCoA || !vCoB || Vec_IntSize(vCoA) != 1 || Vec_IntSize(vCoB) != 1) {
        Abc_Print(-1, "Error: Cnf_DataCollectCoSatNums unexpected result.\n");
        if (vCoA) Vec_IntFree(vCoA);
        if (vCoB) Vec_IntFree(vCoB);
        cleanup();
        return 1;
    }

    // 這個 varCoA / varCoB 就是「cone 唯一輸出」在 copy A / copy B 的 SAT 變數
    int varCoA = Vec_IntEntry(vCoA, 0);
    int varCoB = Vec_IntEntry(vCoB, 0);
    Vec_IntFree(vCoA);
    Vec_IntFree(vCoB);

    // F(A)、F(B) 的 literal（這裡假設 CNF 已經把極性處理好了，所以直接取正 literal）
    lit litF_A = toLitCond(varCoA, 0);
    lit litF_B = toLitCond(varCoB, 0);

    Abc_Print(-1,
        "SAT Debug: varCoA=%d, varCoB=%d, litF_A=%d, litF_B=%d, varXiA=%d, varXiB=%d (idxConeI=%d)\n",
        varCoA, varCoB, litF_A, litF_B, varXiA, varXiB, idxConeI);

    // ---------------------------
    // 8) 對每個「原網路的 PI」 xt，加 xA == xB（除了第 i 個）
    // ---------------------------
    for (int t = 0; t < nPis; ++t) {
        if (t == i) continue;

        int vA = Vec_IntEntry(vPiA, t);
        int vB = Vec_IntEntry(vPiB, t);

        // 不在 cone 裡的 PI（var = -1）直接跳過
        if (vA < 0 || vB < 0)
            continue;

        // xA == xB  ⇔  (¬xA ∨ xB) ∧ (xA ∨ ¬xB)
        lit cls1[2] = { toLitCond(vA, 1), toLitCond(vB, 0) }; // ¬xA ∨ xB
        lit cls2[2] = { toLitCond(vA, 0), toLitCond(vB, 1) }; // xA ∨ ¬xB

        if (!sat_solver_addclause(pSat, cls1, cls1 + 2)) {
            cleanup();
            return 1;
        }
        if (!sat_solver_addclause(pSat, cls2, cls2 + 2)) {
            cleanup();
            return 1;
        }
    }

    bool has_pos = false;
    bool has_neg = false;
    std::string pat_pos, pat_neg;

    // ---------------------------
    // 9a) 0->1：xiA=0, xiB=1, fA=0, fB=1
    // ---------------------------
    {
        Abc_Print(-1,
            "SAT Debug: check 0->1: (xiA=0, xiB=1, fA=0, fB=1)\n");
        Abc_Print(-1,
            "SAT Debug:   using vars xiA=%d, xiB=%d, litF_A=%d, litF_B=%d\n",
            varXiA, varXiB, litF_A, litF_B);

        lit assump[4];
        assump[0] = LitOf(varXiA, 0);  // xiA = 0
        assump[1] = LitOf(varXiB, 1);  // xiB = 1

        assump[2] = litF_A ^ 1;        // fA = 0
        assump[3] = litF_B;            // fB = 1

        int status = sat_solver_solve(pSat, assump, assump + 4,
                                      0, 0, 0, 0);
        Abc_Print(-1,
            "SAT Debug: 0->1 solve status = %d (l_True=%d, l_False=%d)\n",
            status, l_True, l_False);

        if (status == l_True) {
            has_pos = true;
            pat_pos = BuildPatternFromModel(pSat, vPiA, i, nPis);
            Abc_Print(-1,
                "SAT Debug: 0->1 pattern (from vPiA) = %s\n",
                pat_pos.c_str());
        }
    }

    // ---------------------------
    // 9b) 1->0：xiA=1, xiB=0, fA=1, fB=0
    // ---------------------------
    {
        Abc_Print(-1,
            "SAT Debug: check 1->0: (xiA=1, xiB=0, fA=1, fB=0)\n");
        Abc_Print(-1,
            "SAT Debug:   using vars xiA=%d, xiB=%d, litF_A=%d, litF_B=%d\n",
            varXiA, varXiB, litF_A, litF_B);

        lit assump[4];

        // 這裡要和 0->1 不同，代表「相反方向」(1→0)
        assump[0] = LitOf(varXiA, 1);  // xiA = 1
        assump[1] = LitOf(varXiB, 0);  // xiB = 0

        assump[2] = litF_A;            // fA = 1
        assump[3] = litF_B ^ 1;        // fB = 0

        int status = sat_solver_solve(pSat, assump, assump + 4,
                                      0, 0, 0, 0);
        Abc_Print(-1,
            "SAT Debug: 1->0 solve status = %d (l_True=%d, l_False=%d)\n",
            status, l_True, l_False);

        if (status == l_True) {
            has_neg = true;
            pat_neg = BuildPatternFromModel(pSat, vPiA, i, nPis);
            Abc_Print(-1,
                "SAT Debug: 1->0 pattern (from vPiA) = %s\n",
                pat_neg.c_str());
        }
    }

    Abc_Print(-1, "SAT Debug: final has_pos=%d, has_neg=%d\n", has_pos, has_neg);

    // ---------------------------
    // 10) 根據 has_pos/has_neg 分類並輸出
    // ---------------------------
    if (!has_pos && !has_neg) {
        printf("independent\n");
    } else if (has_pos && !has_neg) {
        printf("positive unate\n");
    } else if (!has_pos && has_neg) {
        printf("negative unate\n");
    } else {
        printf("binate\n");
        printf("%s\n", pat_pos.c_str());
        printf("%s\n", pat_neg.c_str());
    }

    cleanup();
    return 0;
}
