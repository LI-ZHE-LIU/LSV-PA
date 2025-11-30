#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"

#include <vector>
#include <string>

// Q1: lsv_unate_bdd <k> <i>
// 檢查第 k 個 PO 的布林函數，對第 i 個 PI 的 unateness
// 並在 binate 的時候輸出兩個 pattern

// 取得某個 BDD 是否為常數 0
static inline bool IsZero(DdManager* dd, DdNode* f) {
    return f == Cudd_ReadLogicZero(dd);
}

// 從一個 BDD 選一個 minterm 出來，轉成 pattern：
//   v == piIndex 用 '-'，其他用 '0' / '1'（'2' 當 '0'）
static std::string PickPatternForPi(
    DdManager* dd,
    DdNode* f,
    Abc_Ntk_t* pNtk,
    int piIndex
) {
    int nPis  = Abc_NtkPiNum(pNtk);
    int nVars = Cudd_ReadSize(dd);

    std::vector<char> cube(nVars);  // Cudd_bddPickOneCube 要 char*
    int ok = Cudd_bddPickOneCube(dd, f, cube.data());
    if (!ok) {
        // 理論上不會發生（因為呼叫前已經確認 f 不是 0）
        return std::string(nPis, '0');
    }

    std::string pat;
    pat.reserve(nPis);
    for (int v = 0; v < nPis; ++v) {
        if (v == piIndex) {
            pat.push_back('-');
        } else {
            // 題目假設 collapse 之後的 BDD 變數順序就是 PI 順序
            char c = (v < nVars) ? cube[v] : '2';  // 0/1/2
            if (c == '1')       pat.push_back('1');
            else /*0 or 2*/     pat.push_back('0');
        }
    }
    return pat;
}

// Debug：印出一個 cube 對應 PI pattern（方便你對照）
// static void DebugPrintOneCubeForPi(
//     DdManager* dd,
//     DdNode* f,
//     Abc_Ntk_t* pNtk,
//     int piIndex
// ) {
//     int nPis  = Abc_NtkPiNum(pNtk);
//     int nVars = Cudd_ReadSize(dd);

//     std::vector<char> cube(nVars);
//     int ok = Cudd_bddPickOneCube(dd, f, cube.data());
//     if (!ok) {
//         Abc_Print(1, "  DebugCube: pick failed (maybe f is zero).\n");
//         return;
//     }

//     Abc_Print(1, "  DebugCube (BDD vars, 0/1/2):");
//     for (int v = 0; v < nVars; ++v) {
//         Abc_Print(1, " %d", (int)cube[v]);
//     }
//     Abc_Print(1, "\n");

//     std::string pat;
//     pat.reserve(nPis);
//     for (int v = 0; v < nPis; ++v) {
//         if (v == piIndex) {
//             pat.push_back('-');
//         } else {
//             char c = (v < nVars) ? cube[v] : '2';
//             if (c == '1')      pat.push_back('1');
//             else if (c == '0') pat.push_back('0');
//             else               pat.push_back('-'); // don't care 用 '-' 印出
//         }
//     }
//     Abc_Print(1, "  DebugCube -> pattern: %s\n", pat.c_str());
// }

// 真正的 command 實作
int Lsv_CommandUnateBdd(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);

    if (argc != 3) {
        Abc_Print(-1, "Usage: lsv_unate_bdd <k> <i>\n");
        Abc_Print(-1, "  k : 0-based primary output index\n");
        Abc_Print(-1, "  i : 0-based primary input index\n");
        return 1;
    }

    if (!pNtk) {
        Abc_Print(-1, "Empty network.\n");
        return 1;
    }

    // 題目要求：read + collapse 之後
    if (!Abc_NtkIsLogic(pNtk)) {
        Abc_Print(-1,
            "Network is not a logic (BDD) network. Please run \"collapse\" first.\n");
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
    int nCis = Abc_NtkCiNum(pNtk);

    Abc_Print(1, "Debug: POs=%d, PIs=%d, CIs=%d\n", nPos, nPis, nCis);

    if (k < 0 || k >= nPos) {
        Abc_Print(-1, "Output index k (%d) is out of range [0, %d).\n", k, nPos);
        return 1;
    }
    if (i < 0 || i >= nPis) {
        Abc_Print(-1, "Input index i (%d) is out of range [0, %d).\n", i, nPis);
        return 1;
    }

    // 1) 拿到 collapse 網路的 BDD manager
    DdManager* dd = (DdManager*)pNtk->pManFunc;
    if (!dd) {
        Abc_Print(-1,
            "This network does not have a BDD manager. Did you run \"collapse\"?\n");
        return 1;
    }

    // 2) 取得第 k 個輸出對應的函數 f ：看 PO 的 fanin 的 BDD
    Abc_Obj_t* pPo    = Abc_NtkPo(pNtk, k);
    Abc_Obj_t* pFanin = Abc_ObjFanin0(pPo);
    if (!pFanin) {
        Abc_Print(-1, "PO %d has no fanin.\n", k);
        return 1;
    }

    DdNode* f = (DdNode*)pFanin->pData;
    if (!f) {
        Abc_Print(-1,
            "PO %d's fanin has no BDD function. Did you run \"collapse\"?\n", k);
        return 1;
    }
    // 注意：f 是由 collapse 建好、ABC 管理的，不要 deref f

    // 3) 第 i 個 PI 對應的變數：用 Cudd_bddIthVar(dd, i)
    //    題目假設 "Given a circuit C in BDD" + 用 collapse ⇒ var順序 = PI順序
    DdNode* xi = Cudd_bddIthVar(dd, i);
    Cudd_Ref(xi);

    // 4) f1 = f|xi=1, f0 = f|xi=0
    DdNode* f1 = Cudd_Cofactor(dd, f, xi);
    Cudd_Ref(f1);

    DdNode* f0 = Cudd_Cofactor(dd, f, Cudd_Not(xi));
    Cudd_Ref(f0);

    // int nVars = Cudd_ReadSize(dd);

    // Abc_Print(1, "Debug: f  BDD summary:\n");
    // Cudd_PrintDebug(dd, f,  nVars, 2);

    // Abc_Print(1, "Debug: f0 BDD summary:\n");
    // Cudd_PrintDebug(dd, f0, nVars, 2);

    // Abc_Print(1, "Debug: f1 BDD summary:\n");
    // Cudd_PrintDebug(dd, f1, nVars, 2);

    // 5) g_plus / g_minus
    // g_plus  = (!f0) & f1   : xi 從 0->1 會讓 f 從 0->1 的地方
    // g_minus = f0 & (!f1)   : xi 從 0->1 會讓 f 從 1->0 的地方
    DdNode* g_plus  = Cudd_bddAnd(dd, Cudd_Not(f0), f1);
    Cudd_Ref(g_plus);
    DdNode* g_minus = Cudd_bddAnd(dd, f0, Cudd_Not(f1));
    Cudd_Ref(g_minus);

    bool has_pos = !IsZero(dd, g_plus);
    bool has_neg = !IsZero(dd, g_minus);

    // Abc_Print(1, "Debug: k=%d i=%d, POs=%d, PIs=%d\n", k, i, nPos, nPis);
    // Abc_Print(1, "Debug: has_pos=%d, has_neg=%d\n", has_pos, has_neg);
    // Abc_Print(1, "Debug: f0 == f1 ? %d\n", (f0 == f1));

    // Abc_Print(1, "Debug: g_plus BDD summary (0->1 region):\n");
    // Cudd_PrintDebug(dd, g_plus, nVars, 2);

    // Abc_Print(1, "Debug: g_minus BDD summary (1->0 region):\n");
    // Cudd_PrintDebug(dd, g_minus, nVars, 2);

    // if (has_pos) {
    //     Abc_Print(1, "Debug: one cube from g_plus (0->1 region):\n");
    //     DebugPrintOneCubeForPi(dd, g_plus, pNtk, i);
    // } else {
    //     Abc_Print(1, "Debug: g_plus is zero, no 0->1 witness.\n");
    // }

    // if (has_neg) {
    //     Abc_Print(1, "Debug: one cube from g_minus (1->0 region):\n");
    //     DebugPrintOneCubeForPi(dd, g_minus, pNtk, i);
    // } else {
    //     Abc_Print(1, "Debug: g_minus is zero, no 1->0 witness.\n");
    // }

    // 6) 判斷 unateness 並輸出
    if (!has_pos && !has_neg) {
        printf("independent\n");
    } else if (has_pos && !has_neg) {
        printf("positive unate\n");
    } else if (!has_pos && has_neg) {
        printf("negative unate\n");
    } else {
        printf("binate\n");
        std::string pat1 = PickPatternForPi(dd, g_plus,  pNtk, i);
        std::string pat2 = PickPatternForPi(dd, g_minus, pNtk, i);
        printf("%s\n", pat1.c_str());
        printf("%s\n", pat2.c_str());
    }

    // 7) Deref 我們自己創造的 BDD node
    Cudd_RecursiveDeref(dd, g_plus);
    Cudd_RecursiveDeref(dd, g_minus);
    Cudd_RecursiveDeref(dd, f0);
    Cudd_RecursiveDeref(dd, f1);
    Cudd_RecursiveDeref(dd, xi);

    return 0;
}
