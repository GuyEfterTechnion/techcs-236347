"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from lambda_calc.syntax import LambdaParser, pretty
from lambda_calc.stdlib import CONSTANTS
from adt.tree import Tree, PreorderWalk


class TypeAssignment:
    def __init__(self, assignments: list):
        self._assignments = assignments.copy()

    def get(self, node: Tree):
        for assign in self._assignments:
            if assign[0] is node:
                return assign[1]


class TypeInference:
    USED_CONSTANTS = CONSTANTS

    def __init__(self, expr: Tree):
        self._next_type_var_id = 0
        self._expr = expr.clone()
        self._assign_type_vars()
        # for n in PreorderWalk(expr):
        #     print('EXPR: ', n, 'TYPE: ', self._type_assignments.get(n))
        self._build_and_solve_constraints()
        # print(self._get_constraint(self._expr))
        print(self._constraints)
        # if any([any(t[0] == 'T' for t in self._constraints[type_var].terminals) for type_var in self._constraints]):
        # # if any([t[0] == 'T' for t in self._get_constraint(self._expr).terminals]):
        #     raise TypeError('insufficient type annotations')
        self._expr_type = self._get_constraint(self._expr).clone()
        self._annotate_expr()

    def __call__(self):
        return self._expr, self._expr_type

    def _annotate_expr(self):
        def annotate_expr_rec(expr: Tree):
            if expr.root in ['\\', '@', 'id', 'let_'] and any(
                    [t[0] == 'T' for t in self._get_constraint(expr).terminals]):
                raise TypeError('insufficient type annotations')

            if expr.root == '\\' and expr.subtrees[0].root == 'id':
                expr.subtrees[0] = Tree(':',
                                        [expr.subtrees[0].clone(),
                                         self._get_constraint(expr.subtrees[0])]
                                        )
                annotate_expr_rec(expr.subtrees[1])
                return

            if expr.root == 'let_' and expr.subtrees[1].root == 'id':
                expr.subtrees[1] = Tree(':',
                                        [expr.subtrees[1].clone(),
                                         self._get_constraint(expr.subtrees[1])]
                                        )
                annotate_expr_rec(expr.subtrees[3])
                annotate_expr_rec(expr.subtrees[5])
                return

            if expr.root == ':':
                return

            for s in expr.subtrees:
                annotate_expr_rec(s)

        annotate_expr_rec(self._expr)

    def _get_next_type_var(self):
        type_var = f"T{self._next_type_var_id}"
        self._next_type_var_id += 1
        return type_var  # Tree('id', [Tree(type_var, [])])

    def _assign_type_vars(self):
        def assign_rec(expr, env: dict):
            if expr.root == 'num':
                type_var = self._get_next_type_var()
                self._constraints[type_var] = Tree('id', [Tree('nat', [])])
                return [(expr, type_var)]
            if expr.root == 'id':
                var = expr.subtrees[0].root
                # important to check in env before in constants, for cases where a bound variable has the same name
                # as a constant
                if env.get(var) is not None:
                    return [(expr, env[var])]
                if var in TypeInference.USED_CONSTANTS:
                    type_var = self._get_next_type_var()
                    self._constraints[type_var] = CONSTANTS[var]
                    return [(expr, type_var)]
                return [(expr, self._get_next_type_var())]

            if expr.root == '\\':
                type_assignment = [(expr, self._get_next_type_var())]
                next_env = env.copy()
                if expr.subtrees[0].root == 'id':
                    bound_var = expr.subtrees[0].subtrees[0].root
                    bound_type_var = self._get_next_type_var()
                    next_env[bound_var] = bound_type_var
                    type_assignment.append((expr.subtrees[0], bound_type_var))

                else:  # encountered type annotation
                    bound_var = expr.subtrees[0].subtrees[0].subtrees[0].root
                    type_anno = expr.subtrees[0].subtrees[1]
                    type_var = self._get_next_type_var()
                    next_env[bound_var] = type_var
                    self._constraints[type_var] = type_anno
                    type_assignment.append((expr.subtrees[0], type_var))

                return type_assignment + assign_rec(expr.subtrees[1], next_env)

            if expr.root == '@':
                return [(expr, self._get_next_type_var())] + assign_rec(expr.subtrees[0], env.copy()) + assign_rec(
                    expr.subtrees[1], env.copy())

            if expr.root == 'let_':
                type_assignment = []
                next_env = env.copy()
                ty_ass = assign_rec(expr.subtrees[3], env.copy())
                type_var_let_exp = TypeAssignment(ty_ass).get(expr.subtrees[3])
                if expr.subtrees[1].root == 'id':
                    bound_var = expr.subtrees[1].subtrees[0].root
                    bound_type_var = type_var_let_exp
                    next_env[bound_var] = bound_type_var
                    type_assignment.append((expr.subtrees[1], bound_type_var))

                else:  # encountered type annotation
                    bound_var = expr.subtrees[1].subtrees[0].subtrees[0].root
                    type_anno = expr.subtrees[1].subtrees[1]
                    bound_type_var = type_var_let_exp
                    next_env[bound_var] = bound_type_var
                    self._constraints[bound_type_var] = type_anno
                    type_assignment.append((expr.subtrees[1], bound_type_var))

                type_assignment += assign_rec(expr.subtrees[5], next_env)
                type_assignment.append((expr, TypeAssignment(type_assignment).get(expr.subtrees[5])))
                return type_assignment + ty_ass

        self._constraints = dict()
        self._type_assignments = assign_rec(self._expr, {})  # CONSTANTS.copy())
        self._type_assignments = TypeAssignment(self._type_assignments)

    def _admit_equiv(self, type_var, ty: Tree):
        def update_type(sub_type: Tree):
            if sub_type.root == 'id':
                if sub_type.subtrees[0].root == type_var:
                    return ty.clone()
                return sub_type.clone()

            # arrow type
            return Tree('->', [update_type(sub_type.subtrees[0]), update_type(sub_type.subtrees[1])])

        self._constraints = {t_var: update_type(self._constraints[t_var]) for t_var in self._constraints}

    def _unify(self, t1: Tree, t2: Tree):
        equal_types = False

        if len(list(PreorderWalk(t1))) == len(list(PreorderWalk(t2))):
            equal_types = True
            for n1, n2 in zip(PreorderWalk(t1), PreorderWalk(t2)):
                if n1.root != n2.root:
                    equal_types = False
                    break

        if equal_types:
            return

        # unified = False

        if t1.root == 'id' and t1.subtrees[0].root[0] == 'T' and t2.root == 'id' and t2.subtrees[0].root[0] == 'T':
            if self._constraints.get(t1.subtrees[0].root) is None:
                if self._constraints.get(t2.subtrees[0].root) is None:
                    self._admit_equiv(t1.subtrees[0].root, t2)
                    self._constraints[t1.subtrees[0].root] = t2.clone()
                    return t2.clone()

                self._constraints[t1.subtrees[0].root] = self._constraints[t2.subtrees[0].root].clone()
                self._admit_equiv(t1.subtrees[0].root, self._constraints[t1.subtrees[0].root])
                return self._constraints[t1.subtrees[0].root].clone()

            if self._constraints.get(t2.subtrees[0].root) is None:
                return self._unify(t2, t1)

            unified_type = self._unify(self._constraints[t1.subtrees[0].root], self._constraints[t2.subtrees[0].root])
            self._constraints[t1.subtrees[0].root] = unified_type.clone()
            self._constraints[t2.subtrees[0].root] = unified_type.clone()
            self._admit_equiv(t1.subtrees[0].root, unified_type)
            self._admit_equiv(t2.subtrees[0].root, unified_type)
            return unified_type.clone()

        if t1.root == 'id' and t1.subtrees[0].root[0] == 'T':
            self._constraints[t1.subtrees[0].root] = t2.clone()
            self._admit_equiv(t1.subtrees[0].root, t2)
            return t2.clone()

        if t2.root == 'id' and t2.subtrees[0].root[0] == 'T':
            # self._constraints[t2.subtrees[0].root] = t1.clone()
            # self._admit_equiv(t2.subtrees[0].root, t1)
            return self._unify(t2, t1)

        if t1.root == '->' and t2.root == '->':
            arg_type = self._unify(t1.subtrees[0], t2.subtrees[0])
            ret_type = self._unify(t1.subtrees[1], t2.subtrees[1])
            return Tree('->', [arg_type, ret_type])

        # if not unified:
        raise TypeError('type mismatch')

    def _get_constraint(self, expr: Tree):
        type_var = self._type_assignments.get(expr)
        if self._constraints.get(type_var) is not None:
            return self._constraints[type_var].clone()

        return Tree('id', [Tree(type_var, [])])

    def _build_and_solve_constraints(self):
        def build_solve_rec(expr: Tree):
            constraint = None
            type_var = None
            if expr.root == '\\':
                constraint = Tree('->', [
                    self._get_constraint(expr.subtrees[0]),
                    self._get_constraint(expr.subtrees[1])
                ])
                type_var = self._type_assignments.get(expr)

            if expr.root == '@':
                constraint = Tree('->', [
                    self._get_constraint(expr.subtrees[1]),
                    self._get_constraint(expr)
                ])
                type_var = self._type_assignments.get(expr.subtrees[0])

            if expr.root == 'let_':
                constraint = self._get_constraint(expr.subtrees[5])
                type_var = self._type_assignments.get(expr)

            if type_var is None:
                return

            # print('type_var: ', type_var)
            if self._constraints.get(type_var) is None:
                self._unify(Tree('id', [Tree(type_var, [])]), constraint)

            else:
                self._unify(self._constraints[type_var], constraint)

            for s in expr.subtrees:
                build_solve_rec(s)

        build_solve_rec(self._expr)


def type_inference(expr: Tree) -> (Tree, Tree):
    """
    Input: an expression.
    Output (tuple):
     * The input expression annotated where every bound variable has a
       type annotation, and a tree representing the type of the whole expression. (type Tree)
     * If encountered a unification error, raise TypeError('type mismatch')
     * If some types cannot be inferred, raise TypeError('insufficient type annotations')
    """
    return TypeInference(expr)()


if __name__ == '__main__':
    # expr0 = LambdaParser()(r"""
    # let add2 = \x. plus x 2 in
    # \f. succ (f True add2)
    # """)
    expr = LambdaParser()(r"""
    let first = \(x : nat) (y : int). x in 
                            let x = \a. (first 5 a) in
                            \(h : ty -> tz) g f. h (g (f (f x)))
    """)

    expr = LambdaParser()(r"""
    \(x : int) (f : nat -> whatever). f (g 3 x)
    """)

    expr = LambdaParser()(r"""\f : nat -> whatever. f (g 3 x)""")

    expr = LambdaParser()(r"""
    \f g (a : real) (z : unreal). f (g a z) (f 5 a)
    """)

    expr = LambdaParser()(r"""
    let first = \(x : nat) (y : int). x in 
    let x = \a. (first 5 a) in
    \(h : ty -> tz) g f. h (g (f (f x)))
    """)

    # expr = LambdaParser()(r"""
    # x
    # """)

    print(pretty(type_inference(expr)[0]))
    print(pretty(type_inference(expr)[1]))

    expr1 = LambdaParser()(r"""
    \f g (a : real) (z : unreal). f (g a z) (f 5 a)
    """)

    expr2 = LambdaParser()(r"""
    \plus (lt : nat -> nat -> bool). lt ((\x. plus x x) 3) ((\x. plus 5 x) 9)
    """)

    expr3 = LambdaParser()(r"""
    let add2 = \(x:nat) (y:ty). plus x 2 in
                \f. succ (f True add2)
    """)
    print(pretty(type_inference(expr3)[0]))

    out1 = LambdaParser()(r"""
    \(f : nat -> (real -> real)) (g : real -> (unreal -> nat)) (a : real) (z : unreal). f (g a z) (f 5 a)
    """)

    out2 = LambdaParser()(r"""
    \(plus : nat -> nat -> nat) (lt : nat -> nat -> bool). lt ((\(x : nat). plus x x) 3) ((\(x : nat). plus 5 x) 9)
    """)

    exprs = [expr1, expr2]
    outs = [out1, out2]

    for expr, out in zip(exprs, outs):
        if expr:
            print(">> Valid expression.")
            print(pretty(expr))
            # print(type_inference(expr))
            print(pretty(type_inference(expr)[0]))
            print(pretty(out))
            print(pretty(out) == pretty(type_inference(expr)[0]))
            print(pretty(type_inference(expr)[1]))
            # from lib.adt.tree.viz import dot_print
            # dot_print(expr)
            # dot_print(type_inference(expr)[0])
        else:
            print(">> Invalid expression.")
