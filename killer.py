#!/usr/bin/env python3
"""杀手数独 (Killer Sudoku) 生成器与求解器。

规则: 9x9 标准数独 + 笼子约束 —— 每个笼子内的数字互不相同,
且之和等于笼子左上角标注的目标和。单格笼子相当于已知数。

纯标准库: argparse / random / sys / itertools。
"""

import argparse
import random
import sys
from itertools import combinations

N = 9
CELLS = [(r, c) for r in range(N) for c in range(N)]


def box_index(r, c):
    return (r // 3) * 3 + c // 3


# ---------------------------------------------------------------------------
# 笼子组合: k 个互不相同的 1-9 数字, 和为 total 的所有集合 (缓存)
# ---------------------------------------------------------------------------
_COMBO_CACHE = {}


def cage_combos(k, total):
    key = (k, total)
    if key not in _COMBO_CACHE:
        _COMBO_CACHE[key] = [
            frozenset(c)
            for c in combinations(range(1, 10), k)
            if sum(c) == total
        ]
    return _COMBO_CACHE[key]


# ---------------------------------------------------------------------------
# 完整数独解生成 (随机回溯)
# ---------------------------------------------------------------------------
def full_sudoku(rng):
    grid = [[0] * N for _ in range(N)]
    row = [set() for _ in range(N)]
    col = [set() for _ in range(N)]
    box = [set() for _ in range(N)]

    def rec(i):
        if i == 81:
            return True
        r, c = CELLS[i]
        digits = list(range(1, 10))
        rng.shuffle(digits)
        for d in digits:
            if d in row[r] or d in col[c] or d in box[box_index(r, c)]:
                continue
            grid[r][c] = d
            row[r].add(d)
            col[c].add(d)
            box[box_index(r, c)].add(d)
            if rec(i + 1):
                return True
            grid[r][c] = 0
            row[r].discard(d)
            col[c].discard(d)
            box[box_index(r, c)].discard(d)
        return False

    if not rec(0):
        raise RuntimeError("数独完整解生成失败")
    return grid


# ---------------------------------------------------------------------------
# 笼子划分: 从完整解出发, 随机生长笼子 (保证笼内数字互不相同)
# ---------------------------------------------------------------------------
def neighbors4(r, c):
    for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        nr, nc = r + dr, c + dc
        if 0 <= nr < N and 0 <= nc < N:
            yield nr, nc


def partition_cages(solution, rng, max_cage=5):
    unassigned = set(CELLS)
    cages = []  # list of (cells, total)
    while unassigned:
        seed = rng.choice(sorted(unassigned))
        unassigned.discard(seed)
        cells = [seed]
        digits = {solution[seed[0]][seed[1]]}
        target = rng.randint(2, max_cage)
        frontier = {nb for nb in neighbors4(*seed) if nb in unassigned}
        while len(cells) < target and frontier:
            pick = rng.choice(sorted(frontier))
            frontier.discard(pick)
            d = solution[pick[0]][pick[1]]
            if d in digits:
                continue  # 笼内不能重复, 跳过该格
            cells.append(pick)
            digits.add(d)
            unassigned.discard(pick)
            for nb in neighbors4(*pick):
                if nb in unassigned:
                    frontier.add(nb)
        # len(cells)==1 时就是单格笼子 (=已知数), 合法
        total = sum(solution[r][c] for r, c in cells)
        cages.append((cells, total))
    return cages


def generate(seed=None, max_cage=5):
    rng = random.Random(seed)
    solution = full_sudoku(rng)
    cages = partition_cages(solution, rng, max_cage)
    return cages, solution


# ---------------------------------------------------------------------------
# 求解器: MRV 回溯 + 笼子组合剪枝
# ---------------------------------------------------------------------------
def solve_killer(cages, limit=1):
    """返回至多 limit 个解, 每个解是 9x9 grid。"""
    grid = [[0] * N for _ in range(N)]
    row = [set() for _ in range(N)]
    col = [set() for _ in range(N)]
    box = [set() for _ in range(N)]
    cell_cage = {}
    cage_assigned = []
    cage_opts = []
    for i, (cells, total) in enumerate(cages):
        for cell in cells:
            cell_cage[cell] = i
        cage_assigned.append(set())
        cage_opts.append(cage_combos(len(cells), total))

    solutions = []

    def candidates(r, c):
        used = row[r] | col[c] | box[box_index(r, c)]
        ci = cell_cage[(r, c)]
        assigned = cage_assigned[ci]
        opts = cage_opts[ci]
        out = []
        for d in range(1, 10):
            if d in used or d in assigned:
                continue
            need = assigned | {d}
            if any(need <= opt for opt in opts):
                out.append(d)
        return out

    empties = set(CELLS)

    def rec():
        if len(solutions) >= limit:
            return True
        # MRV: 选候选最少的空格
        best = None
        best_cands = None
        for (r, c) in empties:
            cands = candidates(r, c)
            if not cands:
                return False
            if best_cands is None or len(cands) < len(best_cands):
                best = (r, c)
                best_cands = cands
                if len(cands) == 1:
                    break
        if best is None:
            solutions.append([row_[:] for row_ in grid])
            return len(solutions) >= limit
        r, c = best
        ci = cell_cage[(r, c)]
        bi = box_index(r, c)
        empties.discard((r, c))
        for d in best_cands:
            grid[r][c] = d
            row[r].add(d)
            col[c].add(d)
            box[bi].add(d)
            cage_assigned[ci].add(d)
            if rec():
                # 回溯清理后继续找更多解 (limit>1 时)
                pass
            grid[r][c] = 0
            row[r].discard(d)
            col[c].discard(d)
            box[bi].discard(d)
            cage_assigned[ci].discard(d)
            if len(solutions) >= limit:
                break
        empties.add((r, c))
        return len(solutions) >= limit

    rec()
    return solutions


# ---------------------------------------------------------------------------
# 独立验证器
# ---------------------------------------------------------------------------
def check_solution(grid, cages):
    """检查 grid 是否满足数独 + 笼子约束。返回 (ok, reason)。"""
    want = set(range(1, 10))
    for r in range(N):
        if set(grid[r]) != want:
            return False, f"第 {r + 1} 行不合法"
    for c in range(N):
        if {grid[r][c] for r in range(N)} != want:
            return False, f"第 {c + 1} 列不合法"
    for b in range(N):
        br, bc = (b // 3) * 3, (b % 3) * 3
        if {grid[br + dr][bc + dc] for dr in range(3) for dc in range(3)} != want:
            return False, f"第 {b + 1} 宫不合法"
    seen = set()
    for cells, total in cages:
        vals = [grid[r][c] for r, c in cells]
        if len(set(vals)) != len(vals):
            return False, "笼内数字重复"
        if sum(vals) != total:
            return False, f"笼子和 {sum(vals)} != 目标 {total}"
        for cell in cells:
            if cell in seen:
                return False, "格子被两个笼子覆盖"
            seen.add(cell)
    if len(seen) != 81:
        return False, "笼子没有覆盖全部 81 格"
    return True, "合法"


# ---------------------------------------------------------------------------
# 渲染
# ---------------------------------------------------------------------------
def cage_tag(i):
    if i < 26:
        return chr(ord("A") + i)
    if i < 52:
        return chr(ord("a") + i - 26)
    return f"#{i}"


def render_puzzle(cages):
    """打印笼子地图 (字母编号) 与各笼目标和。"""
    ids = {}
    for i, (cells, total) in enumerate(cages):
        tag = cage_tag(i)
        first = min(cells)
        for cell in cells:
            ids[cell] = (tag, total if cell == first else None)
    lines = []
    for r in range(N):
        row = []
        for c in range(N):
            tag, total = ids[(r, c)]
            row.append(f"{tag}{total:>2}" if total is not None else f"{tag}  ")
        lines.append(" ".join(f"{x:>4}" for x in row))
        if r % 3 == 2 and r != N - 1:
            lines.append("-" * (5 * N))
    lines.append("")
    lines.append("笼子目标和:")
    for i, (cells, total) in enumerate(cages):
        lines.append(f"  {cage_tag(i)}: {total} (共 {len(cells)} 格)")
    return "\n".join(lines)


def render_grid(grid):
    lines = []
    for r in range(N):
        row = []
        for c in range(N):
            row.append(str(grid[r][c]))
            if c % 3 == 2 and c != N - 1:
                row.append("|")
        lines.append(" ".join(row))
        if r % 3 == 2 and r != N - 1:
            lines.append("-" * 21)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# 自检
# ---------------------------------------------------------------------------
def selftest():
    passed = failed = 0

    def check(name, cond):
        nonlocal passed, failed
        if cond:
            passed += 1
            print(f"  [通过] {name}")
        else:
            failed += 1
            print(f"  [失败] {name}")

    # 1) 手工谜题: 经典数独解 + 手工划分的笼子 (和数手工计算)
    known = [
        [5, 3, 4, 6, 7, 8, 9, 1, 2],
        [6, 7, 2, 1, 9, 5, 3, 4, 8],
        [1, 9, 8, 3, 4, 2, 5, 6, 7],
        [8, 5, 9, 7, 6, 1, 4, 2, 3],
        [4, 2, 6, 8, 5, 3, 7, 9, 1],
        [7, 1, 3, 9, 2, 4, 8, 5, 6],
        [9, 6, 1, 5, 3, 7, 2, 8, 4],
        [2, 8, 7, 4, 1, 9, 6, 3, 5],
        [3, 4, 5, 2, 8, 6, 1, 7, 9],
    ]
    # 笼子: 每行 3 个笼 (3+3+3 格), 和数 = 手工加总
    hand_cages = []
    for r in range(N):
        row = known[r]
        hand_cages.append(([(r, 0), (r, 1), (r, 2)], row[0] + row[1] + row[2]))
        hand_cages.append(([(r, 3), (r, 4), (r, 5)], row[3] + row[4] + row[5]))
        hand_cages.append(([(r, 6), (r, 7), (r, 8)], row[6] + row[7] + row[8]))
    # 手工验算抽查: 第 1 行前三格 5+3+4=12; 第 5 行中间三格 8+5+3=16
    check("手工笼子和抽查 (12 / 16)",
          hand_cages[0][1] == 12 and hand_cages[13][1] == 16)
    ok, _ = check_solution(known, hand_cages)
    check("已知解通过独立验证器", ok)
    sols = solve_killer(hand_cages, limit=1)
    check("手工谜题求解器有解", len(sols) == 1)
    if sols:
        ok2, _ = check_solution(sols[0], hand_cages)
        check("手工谜题的解满足全部约束", ok2)

    # 2) 生成器: 10 个种子, 全部可解且解合法
    all_ok = True
    for seed in range(10):
        cages, _gen_sol = generate(seed=seed)
        sols = solve_killer(cages, limit=1)
        if not sols:
            all_ok = False
            print(f"    seed={seed}: 无解!")
            break
        ok3, reason = check_solution(sols[0], cages)
        if not ok3:
            all_ok = False
            print(f"    seed={seed}: 解非法: {reason}")
            break
        # 笼内无重复 (验证器已含, 这里显式再查一次生成器不变式)
        for cells, total in cages:
            vals = [_gen_sol[r][c] for r, c in cells]
            assert len(set(vals)) == len(vals), "生成器笼内重复"
    check("10 个种子生成谜题全部可解且合法", all_ok)

    print(f"自检结果: {passed} 通过, {failed} 失败")
    return failed == 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(
        prog="killer",
        description="杀手数独: 生成谜题 / 回溯求解。纯标准库。",
    )
    ap.add_argument("--seed", type=int, default=None, help="随机种子 (可复现)")
    ap.add_argument("--solve", action="store_true", help="生成后同时求解并打印答案")
    ap.add_argument("--max-cage", type=int, default=5,
                    help="笼子最大格数 (默认 5)")
    ap.add_argument("--selftest", action="store_true", help="运行内置自检")
    args = ap.parse_args(argv)

    if args.selftest:
        ok = selftest()
        return 0 if ok else 1

    if args.max_cage < 2 or args.max_cage > 9:
        print("错误: --max-cage 范围 2~9", file=sys.stderr)
        return 2

    cages, _solution = generate(seed=args.seed, max_cage=args.max_cage)
    print(f"杀手数独 (seed={args.seed}, {len(cages)} 个笼子):\n")
    print(render_puzzle(cages))

    if args.solve:
        sols = solve_killer(cages, limit=1)
        if not sols:
            print("\n求解失败: 无解 (不应发生, 请报告 bug)")
            return 1
        print("\n答案:\n")
        print(render_grid(sols[0]))
        ok, reason = check_solution(sols[0], cages)
        print(f"\n验证: {reason}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
