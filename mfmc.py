"""Generate CNF instances for the computer-assisted proof of Proposition 16.

For a given dimension --d and family (--general or --up-monotone), iterates over
all admissible weight functions (d, tau, w) and writes one DIMACS CNF per instance
to <out-dir>/d<N>[up]/ (default out-dir: instances/). Each CNF is satisfiable iff
a set S with the relevant properties exists; the proposition asserts none does, so
each must be UNSAT. With --self-check, instances are instead solved in memory with
PySAT (no files written) as an independent confirmation that each is UNSAT.
See the README.
"""
import argparse
import itertools
import os
import time
from collections.abc import Sequence

FREE = 2    # free coordinate
USE_NEG, USE_POS, USE_NEITHER = 0, 1, 2 # cover contains \bar{i}, i, or neither


class MFMCInstanceEncoder:
    def __init__(self, d: int, tau: int, w: Sequence[int],
                 tight: bool, up_monotone: bool, file_name: str | None) -> None:
        if d > 12:
            raise ValueError("Cube-idealness for d >= 13 is not implemented.")
        self.d = d
        self.tau = tau
        self.w = list(w)
        for i in range(d):
            if not (1 <= w[i] <= tau // 2):
                raise ValueError(f"w[{i}] = {w[i]} must satisfy 1 <= w_i <= tau//2 = {tau // 2}")
        self.up_monotone = up_monotone
        self.tight = tight
        self.file_name = file_name

        if self.file_name is None:
            from pysat.solvers import Cadical195
            self.solver = Cadical195()
        else:
            self.clauses: list[list[int]] = []
        self.x = list(range(1, (1<<d)+1))
        self.var_count = 1 << d
        self.clause_count = 0
        self.y = {}
        for restriction in itertools.product((0, 1, FREE), repeat = self.d):
            # (0, 1, FREE) product order is lexicographic so each restriction's two children
            # are already computed
            first_free = next((i for i in range(self.d) if restriction[i] == FREE), self.d)
            if first_free == self.d:
                self.y[restriction] = self.x[sum((1<<i) for i in range(self.d) if restriction[i] == 1)]
            else:
                self.y[restriction] = self.new_iff_or([
                    self.y[restriction[:first_free] + (a,) + restriction[first_free + 1:]]
                    for a in (0, 1)
                ])

        if self.up_monotone:
            for b in range(1 << self.d):
                for i in range(self.d):
                    if (b & (1 << i)) == 0:
                        self.add_clause([-self.x[b], self.x[b ^ (1 << i)]])

    def new_var(self):
        """Allocates and returns a new auxiliary SAT variable."""
        self.var_count += 1
        return self.var_count

    def add_clause(self, clause):
        """Adds the clause."""
        self.clause_count += 1
        if self.file_name is None:
            self.solver.add_clause(clause)
        else:
            self.clauses.append(clause)

    def new_iff_and(self, lits):
        """Returns a literal z such that z <=> (lits[0] AND lits[1] AND ... )."""
        if len(lits) == 1:
            return lits[0]
        z = self.new_var()
        self.add_clause([z] + [-lit for lit in lits])
        for lit in lits:
            self.add_clause([-z, lit])
        return z

    def new_iff_or(self, lits):
        """Returns a literal z such that z <=> (lits[0] OR lits[1] OR ... )."""
        if len(lits) == 1:
            return lits[0]
        z = self.new_var()
        self.add_clause([-z] + lits)
        for lit in lits:
            self.add_clause([z, -lit])
        return z

    def add_strictly_polar(self):
        """Adds strict polarity."""
        for restriction in itertools.product((0, 1, FREE), repeat = self.d):
            free_coords = [i for i in range(self.d) if restriction[i] == FREE]
            num_free = len(free_coords)
            if num_free < 3:
                continue
            fixed_part = sum(1<<i for i in range(self.d) if restriction[i] == 1)
            free_mask = sum(1<<i for i in free_coords)
            clause = []
            # Case 1: the restriction contains two antipodal points
            for p_free in range(1<<(num_free-1)):
                p = fixed_part + sum(1<<free_coords[i] for i in range(num_free-1) if (p_free & (1<<i)))
                clause.append(self.new_iff_and([self.x[p], self.x[p ^ free_mask]])) # Both p and its antipode in the restriction are feasible
            # Case 2: the restriction is contained in a hyperplane {p: p_i = a}
            for i in free_coords:
                for a in (0, 1):
                    side = restriction[:i] + (a,) + restriction[i + 1:]
                    clause.append(-self.y[side])
            self.add_clause(clause)

    def add_width_length(self, m, max_member_size, max_cover_size):
        """Adds the constraint that each m-element minor of each localization
           contains a member of size <= max_member_size or a cover of size <= max_cover_size."""
        for K in itertools.combinations(range(self.d), m):
            outside_coords = [i for i in range(self.d) if i not in set(K)]
            op_choices = (0, FREE) if self.up_monotone else (0, 1, FREE)
            for minor_ops in itertools.product(op_choices, repeat = self.d-m):
                minor_restriction = [FREE] * self.d
                for i in range(self.d-m):
                    minor_restriction[outside_coords[i]] = minor_ops[i]
                max_p = 1 if self.up_monotone else (1<<m)
                for p in range(max_p):
                    clause = []
                    # localization contains a set of size <= max_member_size
                    for D in itertools.combinations(range(m), m - max_member_size):
                        member_restriction = minor_restriction.copy()
                        for i in D:
                            member_restriction[K[i]] = (p >> i) & 1
                        clause.append(self.y[tuple(member_restriction)])
                    # localization has a cover of size <= max_cover_size
                    for B in itertools.combinations(range(m), max_cover_size):
                        cover_restriction = minor_restriction.copy()
                        for i in B:
                            cover_restriction[K[i]] = (p >> i) & 1
                        clause.append(-self.y[tuple(cover_restriction)])
                    self.add_clause(clause)

    def add_cube_ideal(self):
        """Adds cube-idealness."""
        P = [(5,2,3), (7,2,4), (8,3,3), (9,2,5), (11,2,6), (11,3,4), (11,4,3)]
        for m, r, s in P:
            if m <= self.d:
                self.add_width_length(m, r-1, s-1)

    def cover_to_empty_restriction(self, B):
        """Returns the restriction that is empty exactly if B is a cover.
            Element i in the cover (USE_POS) forces {p: p_i = 0} empty.
            Element bar{i} in the cover (USE_NEG) forces {p: p_i = 1} empty.
        """
        return tuple((FREE if b == USE_NEITHER else (0 if b == USE_POS else 1)) for b in B)

    def cover_weight(self, B):
        """Returns the weight of a cover B."""
        return sum(self.w[i] if B[i] == USE_POS else self.tau - self.w[i]
                   for i in range(self.d) if B[i] != USE_NEITHER)

    def add_no_small_covers(self, max_forbidden_weight):
        """Forbids covers B with w(B) <= max_forbidden_weight and |B ∩ {i, ī}| <= 1 for each i."""
        for B in itertools.product((USE_NEG, USE_POS, USE_NEITHER), repeat = self.d):
            if self.cover_weight(B) <= max_forbidden_weight:
                self.add_clause([self.y[self.cover_to_empty_restriction(B)]])

    def add_mates(self):
        """Adds the mate condition for each feasible point p in S."""
        candidates = [] # Mates B satisfy tau <= w(B) <= |B|+tau-2, keep only these sets.
        cover_choices = (USE_POS, USE_NEITHER) if self.up_monotone else (USE_NEG, USE_POS, USE_NEITHER)
        for B in itertools.product(cover_choices, repeat = self.d):
            weight = self.cover_weight(B)
            I0_mask = sum(1 << i for i in range(self.d) if B[i] == USE_POS)
            I1_mask = sum(1 << i for i in range(self.d) if B[i] == USE_NEG)
            cover_size = sum(1 for b in B if b != USE_NEITHER)
            if self.tau <= weight <= cover_size + self.tau - 2:
                cover_lit = -self.y[self.cover_to_empty_restriction(B)]
                candidates.append((weight, I0_mask, I1_mask, cover_lit))
        for p in range(1 << self.d):
            clause = [-self.x[p]]
            for weight, I0_mask, I1_mask, cover_lit in candidates:
                intersection_size = (
                        (p & I0_mask).bit_count() +
                        ((~p) & I1_mask).bit_count()
                )
                if weight <= intersection_size + self.tau - 2:
                    clause.append(cover_lit)
            self.add_clause(clause)

    def add_zero_infeasible(self):
        """Adds 0 not in S."""
        self.add_clause([-self.x[0]])

    def add_lex_geq(self, A, B):
        """Adds A >= B lexicographically."""
        assert len(A) == len(B)
        eq_prefix = self.new_var()
        self.add_clause([eq_prefix])
        for k in range(len(A)):
            # If the prefix is equal, forbid A[k]=0, B[k]=1
            self.add_clause([-eq_prefix, -B[k], A[k]])
            if k + 1 < len(A):
                # Given B[k] <= A[k], equality holds if A[k]==0 OR B[k]==1
                eq_next = self.new_var()
                # If prefix is equal and A[k]=0 or B[k] = 1, prefix remains equal (since A[k] >= B[k]).
                self.add_clause([-eq_prefix, A[k], eq_next])
                self.add_clause([-eq_prefix, -B[k], eq_next])
                eq_prefix = eq_next

    def swap_coordinates(self, p, i, j):
        """Returns the point obtained from p by swapping coordinates i and j."""
        if ((p >> i) & 1) == ((p >> j) & 1):
            return p
        return p ^ ((1 << i) | (1 << j))

    def add_weight_symmetry_breaking(self):
        """Breaks some coordinate-permutation symmetries among coordinates with equal w[i].
           Namely, adds lex constraints for transpositions of equal-weight coordinate pairs.
        """
        weight_blocks = [[] for _ in range(self.tau + 1)]
        for i in range(self.d):
            weight_blocks[self.w[i]].append(i)

        for block in weight_blocks:
            for i, j in itertools.combinations(block, 2):
                A = [self.x[p] for p in range(1 << self.d)]
                B = [self.x[self.swap_coordinates(p, i, j)] for p in range(1 << self.d)]
                self.add_lex_geq(A, B)

    def solve(self):
        """Solves using pysat."""
        if self.file_name is not None:
            raise ValueError("Output filename was provided.")
        start = time.perf_counter()
        is_solvable = self.solver.solve()
        end = time.perf_counter()
        return is_solvable, end-start

    def write_clauses(self):
        """Writes cnf file."""
        if self.file_name is None:
            raise ValueError("No output filename was provided.")
        with open(self.file_name, "w") as f:
            f.write(f"c d={self.d} tau={self.tau} w={','.join(map(str, self.w))} "
                    f"tight={self.tight} up_monotone={self.up_monotone}\n")
            f.write(f"p cnf {self.var_count} {self.clause_count}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")

def _build_model(d: int, tau: int, w: Sequence[int], tight: bool,
                 up_monotone: bool, filename: str | None) -> "MFMCInstanceEncoder":
    model = MFMCInstanceEncoder(d, tau, list(w), tight, up_monotone, filename)
    model.add_strictly_polar()
    model.add_cube_ideal()
    model.add_mates()
    model.add_zero_infeasible()
    model.add_no_small_covers(tau if tight else tau-1)
    model.add_weight_symmetry_breaking()
    return model

def write_instance(d: int, tau: int, w: Sequence[int], tight: bool,
                    up_monotone: bool, filename: str) -> None:
    model = _build_model(d, tau, w, tight, up_monotone, filename)
    model.write_clauses()

def solve_instance(d: int, tau: int, w: Sequence[int], tight: bool,
                    up_monotone: bool) -> tuple[list[int], int, bool, float]:
    model = _build_model(d, tau, w, tight, up_monotone, None)
    is_solvable, solve_time = model.solve()
    model.solver.delete()
    return (list(w), tau, is_solvable, solve_time)

def is_admissible(d: int, tau: int, w: Sequence[int]) -> int:
    """Admissibility test. The checked inequality is the paper's
         s/(s-tau) - (tau-2)/k + 1 <= sum_{i=1}^k ((k+1-i)(s-tau+i-1)/(ks)) |E_i|
       multiplied through by k*s*(s-tau) > 0.
       Returns 2 iff s = d+1 is the only feasible s (tightly admissible).
    """
    E_cnt = [0] * tau # = |E_i| = number of elements of weight i
    for i in range(d):
        E_cnt[w[i]] += 1
        E_cnt[tau-w[i]] += 1
    for s in range(tau+1, d+2):
        if all(k*s*s - s*(tau-2)*(s-tau) + k*s*(s-tau) <=
               sum((k+1-i)*(s-tau+i-1)*(s-tau)*E_cnt[i] for i in range(1, k+1))
            for k in range(1, tau)):
            return (1 if s < d+1 else 2)
    return 0

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Generate CNF instances.")
    parser.add_argument("--d", type=int, required=True)
    fam = parser.add_mutually_exclusive_group(required=True)
    fam.add_argument("--up-monotone", dest="up_monotone", action="store_true")
    fam.add_argument("--general",     dest="up_monotone", action="store_false")
    parser.add_argument("--out-dir", default="instances")
    parser.add_argument("--self-check", action="store_true",
                        help="solve using pysat instead of writing CNFs")
    args = parser.parse_args()

    if not args.self_check:
        family = "up" if args.up_monotone else ""
        out_dir = os.path.join(args.out_dir, f"d{args.d}{family}")
        os.makedirs(out_dir, exist_ok=True)

    instance_no = 0
    cnt_sat = 0
    for tau in range(3, args.d + 1):
        for w in itertools.combinations_with_replacement(range(1, tau // 2 + 1), args.d):
            a = is_admissible(args.d, tau, w)
            if not a:
                continue
            instance_no += 1
            kind = "tight" if a == 2 else "adm."
            desc = f"[{instance_no:03d}] d={args.d} tau={tau:>2} {kind:<5} w=({','.join(map(str, w))})"
            if args.self_check:
                *_, solvable, t = solve_instance(args.d, tau, w, a == 2, args.up_monotone)
                if solvable:
                    cnt_sat += 1
                status = "SAT (!)" if solvable else "UNSAT"
                print(f"{desc}  {status:<7}  {t:7.3f}s")
            else:
                path = os.path.join(out_dir, f"d{args.d}{family}_instance{instance_no:03d}.cnf")
                write_instance(args.d, tau, w, a == 2, args.up_monotone, path)
                print(f"{desc}  ->  {path}")

    if args.self_check:
        verdict = "all UNSAT as expected" if cnt_sat == 0 else f"*** {cnt_sat} UNEXPECTED SAT ***"
        print(f"\n{instance_no} admissible instance(s) solved: {instance_no - cnt_sat} UNSAT, {cnt_sat} SAT  ({verdict})")
    else:
        print(f"\n{instance_no} CNF instance(s) written to {out_dir}/")
