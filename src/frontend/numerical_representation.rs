//! The finite representation grammar of edition 2026. Parsing a representation
//! does not authorize storage or select an exact coefficient model.
use super::*;

impl Parser {
    pub(super) fn numerical_representation(
        &mut self,
    ) -> Result<NumericalRepresentation, Diagnostic> {
        let width = self.advance();
        if !width.is("F32") && !width.is("F64") {
            let message = if width.is("Complex") {
                "complex storage requires an explicit representation such as `F64<CC>`"
            } else {
                "expected a numerical representation F32<RR>, F32<CC>, F64<RR> or F64<CC>"
            };
            return Err(diagnostic("E_TYPE", message, width.span));
        }
        if !self.consume("<") {
            return Err(diagnostic(
                "E_TYPE",
                "expected an explicit numerical representation target in angle brackets, RR or CC",
                width.span,
            ));
        }
        let target = self.advance();
        let complex = match &target.kind {
            TokenKind::Name(name) if name == "RR" => false,
            TokenKind::Name(name) if name == "CC" => true,
            _ => {
                return Err(diagnostic(
                    "E_TYPE",
                    "a numerical representation target must be RR or CC",
                    target.span,
                ));
            }
        };
        self.type_close()?;
        Ok(match (width.is("F32"), complex) {
            (true, false) => NumericalRepresentation::Real32,
            (true, true) => NumericalRepresentation::Complex32,
            (false, false) => NumericalRepresentation::Real64,
            (false, true) => NumericalRepresentation::Complex64,
        })
    }
}
