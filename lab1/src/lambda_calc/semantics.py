from lambda_calc.syntax import LambdaParser, pretty
from typing import Optional
from adt.tree import Tree


class LambdaInterpreter(object):
    @staticmethod
    def _get_reduced_redex(e1, x, e2):
        def rec_replace(e):
            if len(e.subtrees) == 0:
                return e.clone()

            if e.root == '\\' and e.subtrees[0].subtrees[0].root == x:
                return e.clone()

            if e.root == 'id' and e.subtrees[0].root == x:
                return e2.clone()

            new_subtrees = [rec_replace(s) for s in e.subtrees]
            return Tree(e.root, new_subtrees)

        return rec_replace(e1)

    @staticmethod
    def _beta_reduce(expr):
        def build_reduced_tree(expr, redex_found):
            if (not redex_found) and LambdaInterpreter._is_redex(expr):
                lambd = expr.subtrees[0]
                x = lambd.subtrees[0].subtrees[0].root
                e1 = lambd.subtrees[1]
                e2 = expr.subtrees[1]

                return LambdaInterpreter._get_reduced_redex(e1, x, e2), True

            new_subtrees = []
            for s in expr.subtrees:
                if redex_found:
                    new_subtrees.append(s.clone())
                else:
                    new_s, redex_found = build_reduced_tree(s, redex_found)
                    new_subtrees.append(new_s)

            return Tree(expr.root, new_subtrees), redex_found

        return build_reduced_tree(expr, False)

    @staticmethod
    def _is_redex(expr):
        return expr.root == '@' and expr.subtrees[0].root == '\\'

    def __call__(self, program_text: str) -> Optional[str]:
        expr = LambdaParser()(program_text)
        if not expr:
            return None

        while True:
            expr, redex_found = self._beta_reduce(expr)
            if not redex_found:
                break

        return pretty(expr)


if __name__ == '__main__':
    print(LambdaInterpreter()(r"(\n. \a. \b. (a (n a b))) (\x. \y. x x y)"))
