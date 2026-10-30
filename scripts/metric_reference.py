"""Selected constant real metrics and independently checked musical evidence.

Finite Python reference for #264. Nothing here registers an AD primitive or
certifies Vastitas/Lean Core. The metric-free module never imports this module.
"""

from dataclasses import dataclass

from metric_free_reference import (
    IDENTITY, Cotangent, Frame, Invalid, Point, Tangent, cotangent_pullback,
    determinant, differential, identifier, inverse, matrix, matvec, multiply,
    require_coordinate_change, require_point, transpose, vector,
)


@dataclass(frozen=True)
class Metric:
    """Named constant symmetric form; nondegeneracy/positivity are NOT implicit."""

    frame: Frame
    metric_id: str
    revision: str
    gram: tuple

    def __post_init__(self):
        if type(self.frame) is not Frame:
            raise Invalid("INVALID_FRAME", "expected a named real-plane frame")
        identifier(self.metric_id, "metric_id")
        identifier(self.revision, "revision")
        object.__setattr__(self, "gram", matrix(self.gram))
        if self.gram != transpose(self.gram):
            raise Invalid("NOT_SYMMETRIC", "a metric candidate must be symmetric")


@dataclass(frozen=True)
class FiberMetric:
    metric: Metric
    point: Point

    def __post_init__(self):
        if type(self.metric) is not Metric:
            raise Invalid("MISSING_METRIC", "select a metric explicitly")
        require_point(self.point, self.metric.frame)


@dataclass(frozen=True)
class NondegenerateEvidence:
    subject: FiberMetric
    inverse_gram: tuple

    def __post_init__(self):
        if type(self.subject) is not FiberMetric:
            raise Invalid("INVALID_EVIDENCE", "expected a metric at the exact basepoint")
        object.__setattr__(self, "inverse_gram", matrix(self.inverse_gram))


@dataclass(frozen=True)
class RiemannianEvidence:
    subject: FiberMetric
    nondegenerate: NondegenerateEvidence
    leading_minors: tuple

    def __post_init__(self):
        if type(self.subject) is not FiberMetric or type(self.nondegenerate) is not NondegenerateEvidence:
            raise Invalid("INVALID_EVIDENCE", "expected a metric subject and inverse evidence")
        object.__setattr__(self, "leading_minors", vector(self.leading_minors))


def check_nondegenerate(expected, evidence):
    """Full-subject binding, followed by two exact inverse identities."""
    if type(expected) is not FiberMetric:
        raise Invalid("MISSING_METRIC", "supply the independently selected metric fiber")
    if type(evidence) is not NondegenerateEvidence:
        raise Invalid("MISSING_NONDEGENERACY", "sharp requires explicit inverse evidence")
    if evidence.subject != expected:
        raise Invalid("EVIDENCE_SUBJECT_MISMATCH", "wrong object/base/frame/point/metric/revision/data")
    gram, candidate = expected.metric.gram, evidence.inverse_gram
    if multiply(gram, candidate) != IDENTITY or multiply(candidate, gram) != IDENTITY:
        raise Invalid("INVALID_INVERSE", "both G B = I and B G = I must hold exactly")
    return evidence


def certify_nondegenerate(subject):
    if type(subject) is not FiberMetric:
        raise Invalid("MISSING_METRIC", "supply the selected metric fiber")
    evidence = NondegenerateEvidence(subject, inverse(subject.metric.gram))
    return check_nondegenerate(subject, evidence)


def check_riemannian(expected, evidence):
    if type(evidence) is not RiemannianEvidence:
        raise Invalid("MISSING_POSITIVITY", "nondegenerate alone is not Riemannian")
    if evidence.subject != expected:
        raise Invalid("EVIDENCE_SUBJECT_MISMATCH", "positivity belongs to a different subject")
    check_nondegenerate(expected, evidence.nondegenerate)
    gram = expected.metric.gram
    actual = (gram[0][0], determinant(gram))
    if evidence.leading_minors != actual:
        raise Invalid("MINOR_MISMATCH", "claimed minors differ from the selected matrix")
    if not all(minor > 0 for minor in actual):
        raise Invalid("NOT_POSITIVE_DEFINITE", "Sylvester's two exact inequalities fail")
    return evidence


def certify_riemannian(subject):
    nd = certify_nondegenerate(subject)
    evidence = RiemannianEvidence(subject, nd, (subject.metric.gram[0][0], determinant(subject.metric.gram)))
    return check_riemannian(subject, evidence)


@dataclass(frozen=True)
class FlatResult:
    subject: FiberMetric
    argument: Tangent
    value: Cotangent


@dataclass(frozen=True)
class SharpResult:
    subject: FiberMetric
    argument: Cotangent
    evidence: NondegenerateEvidence
    value: Tangent


def require_argument(subject, argument, kind):
    if type(subject) is not FiberMetric:
        raise Invalid("MISSING_METRIC", "select the metric at this basepoint explicitly")
    if type(argument) is not kind:
        raise Invalid("VARIANCE_MISMATCH", f"expected {kind.__name__}")
    if argument.point != subject.point:
        raise Invalid("FIBER_MISMATCH", "argument must use the selected metric fiber")


def flat(subject, tangent):
    require_argument(subject, tangent, Tangent)
    return FlatResult(subject, tangent, Cotangent(subject.point, matvec(subject.metric.gram, tangent.components)))


def sharp(subject, alpha, evidence):
    require_argument(subject, alpha, Cotangent)
    check_nondegenerate(subject, evidence)
    return SharpResult(subject, alpha, evidence,
                       Tangent(subject.point, matvec(evidence.inverse_gram, alpha.components)))


def gradient(function, point, *, using, evidence):
    """Derived helper only: metric-free df, then explicitly selected sharp."""
    return sharp(FiberMetric(using, point), differential(function, point), evidence)


def reexpress_metric(change, metric):
    require_coordinate_change(change)
    if type(metric) is not Metric or metric.frame != change.target:
        raise Invalid("FIBER_MISMATCH", "metric must use the target coordinate frame")
    gram = multiply(multiply(transpose(change.forward), metric.gram), change.forward)
    return Metric(change.source, metric.metric_id, metric.revision, gram)


def check_metric_transport(change, metric, claimed):
    expected = reexpress_metric(change, metric)
    if type(claimed) is not Metric or claimed != expected:
        raise Invalid("METRIC_TRANSPORT_MISMATCH", "expected the same selected metric with A^T G A")
    return expected


def check_gradient_transport(change, point, metric, alpha, target_claim, source_claim):
    """Recheck both sharp results, metric identity and tangent transport separately.

    The original metric/alpha and the coordinate change are independent inputs,
    not inferred from either untrusted result record.
    """
    require_coordinate_change(change)
    target = FiberMetric(metric, change.at(point))
    source_metric = reexpress_metric(change, metric)
    source = FiberMetric(source_metric, point)
    source_alpha = cotangent_pullback(change.as_map(), point, alpha)
    for subject, argument, claim in ((target, alpha, target_claim), (source, source_alpha, source_claim)):
        if type(claim) is not SharpResult:
            raise Invalid("INVALID_GRADIENT_CLAIM", "expected a sharp result with selected metric evidence")
        actual = sharp(subject, argument, claim.evidence)
        if claim != actual:
            raise Invalid("GRADIENT_MISMATCH", "sharp result does not match its independently supplied subject/input")
    if change.push_tangent(source_claim.value) != target_claim.value:
        raise Invalid("GRADIENT_TRANSPORT_MISMATCH", "expected A grad_u = grad_x")
    return source_claim
