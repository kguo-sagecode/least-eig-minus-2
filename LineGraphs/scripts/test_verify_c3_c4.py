"""Regression checks for complete, standard-axiom audit output."""
import unittest

from verify_c3_c4 import check_axiom_audit


class AxiomAuditTests(unittest.TestCase):
    source = "#print axioms First\n#print axioms Second\n"
    complete = (
        "'First' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'Second' does not depend on any axioms\n"
    )

    def test_complete_standard_audit(self):
        check_axiom_audit(self.source, self.complete)

    def test_empty_output_fails(self):
        with self.assertRaisesRegex(ValueError, "Missing axiom audit declarations"):
            check_axiom_audit(self.source, "")

    def test_partial_output_fails(self):
        with self.assertRaisesRegex(ValueError, "Second"):
            check_axiom_audit(self.source, self.complete.splitlines()[0])

    def test_indented_directive_partial_output_fails(self):
        """Indented Lean directives must remain in the required audit inventory."""
        for indent in ("  ", "\t"):
            with self.subTest(indent=indent):
                source = f"#print axioms First\n{indent}#print axioms Second\n"
                check_axiom_audit(source, self.complete)
                with self.assertRaisesRegex(ValueError, "Second"):
                    check_axiom_audit(source, self.complete.splitlines()[0])

    def test_primed_declaration_names(self):
        """Primed theorem names match Lean's quoted axiom output."""
        source = self.source.replace("First", "First'").replace("Second", "Second'")
        output = self.complete.replace("First", "First'").replace("Second", "Second'")
        check_axiom_audit(source, output)
        with self.assertRaisesRegex(ValueError, "Second'"):
            check_axiom_audit(source, output.splitlines()[0])

    def test_nonstandard_dependency_fails(self):
        with self.assertRaisesRegex(ValueError, "Unexpected axioms"):
            check_axiom_audit(self.source, self.complete.replace("propext", "custom.invalid"))

    def test_empty_inventory_fails(self):
        with self.assertRaises(ValueError):
            check_axiom_audit("", self.complete)


if __name__ == "__main__":
    unittest.main()
