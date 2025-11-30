#!/usr/bin/env bash
# 使用方式：
#   ./run_abc_unate.sh <path/to/circuit.blif> [k] [i]
# 範例：
#   ./run_abc_unate.sh lsv/pa1/benchmarks/alu_sop.blif 2 1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR" || exit 1

# 參數檢查
if [ $# -lt 1 ]; then
  echo "Usage: $0 <blif_file> [k] [i]"
  exit 1
fi

BLIF="$1"
K="${2:-0}"   # 預設 k = 0
I="${3:-0}"   # 預設 i = 0

if [ ! -f "$BLIF" ]; then
  echo "Error: BLIF file '$BLIF' not found."
  exit 1
fi

echo "Building abc ..."
if [ -n "$CC" ] && [ -n "$CXX" ]; then
  make -j"$(nproc)" CC="$CC" CXX="$CXX" || { echo "make failed"; exit 1; }
else
  make -j"$(nproc)" || { echo "make failed"; exit 1; }
fi
echo

# 先跑 BDD 版
echo "Running ABC on $BLIF with lsv_unate_bdd $K $I ..."
CMD="read $BLIF; collapse; comb; lsv_unate_bdd $K $I"
./abc -c "$CMD"
echo

# 再跑 SAT 版
echo "Running ABC on $BLIF with lsv_unate_sat $K $I ..."
CMD="read $BLIF; strash; comb; lsv_unate_sat $K $I"
./abc -c "$CMD"
