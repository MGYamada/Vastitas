//! Source-only, finite binary64 payload spelling. Accepted decimal values are
//! compared with an integer reconstruction of the candidate's exact value; the
//! host parser's rounding never authorizes an inexact source literal.

use std::cmp::Ordering;

const SIGN: u64 = 1 << 63;
const FRACTION: u64 = (1 << 52) - 1;

pub(super) fn bits(text: &str, negative: bool) -> Result<u64, String> {
    let magnitude = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        hex_bits(hex)?
    } else {
        decimal_bits(text, negative)?
    };
    if magnitude == 0 && negative {
        return Err(format!(
            "signed zero requires explicit bits (binary64 payload {SIGN}); use f64_bits or complex_bits"
        ));
    }
    Ok(magnitude | if negative { SIGN } else { 0 })
}

fn exponent(text: &str) -> Result<i64, String> {
    if text.trim_start_matches(['+', '-']).is_empty()
        || !text
            .trim_start_matches(['+', '-'])
            .bytes()
            .all(|b| b.is_ascii_digit())
    {
        return Err("expected a signed decimal exponent".into());
    }
    text.parse()
        .map_err(|_| "literal exponent exceeds the supported signed 64-bit range".into())
}

fn mantissa(text: &str, radix: u32) -> Result<(String, usize), String> {
    let mut pieces = text.split('.');
    let whole = pieces.next().unwrap();
    let fraction = pieces.next().unwrap_or("");
    if pieces.next().is_some()
        || (whole.is_empty() && fraction.is_empty())
        || !whole
            .chars()
            .chain(fraction.chars())
            .all(|c| c.is_ascii() && c.is_digit(radix))
    {
        return Err(
            "expected a finite decimal or hexadecimal literal without suffixes or separators"
                .into(),
        );
    }
    Ok((format!("{whole}{fraction}"), fraction.len()))
}

fn hex_bits(text: &str) -> Result<u64, String> {
    let (significand, power) = text
        .split_once(['p', 'P'])
        .ok_or("hexadecimal payloads require a binary exponent, for example 0x1.8p0")?;
    let power = exponent(power)?;
    let (digits, fraction) = mantissa(significand, 16)?;
    let nonzero = digits.trim_start_matches('0');
    if nonzero.is_empty() {
        return Ok(0);
    }
    let significant = nonzero.trim_end_matches('0');
    // Removing hex zeroes bounds conversion even for long exact spellings.
    // Fourteen remaining hex digits can contain at most 53 significant bits
    // after the remaining one-to-three trailing zero bits are removed.
    if significant.len() > 14 {
        return Err("hexadecimal literal is not exactly representable in binary64 (more than 53 significant bits)".into());
    }
    let mut value =
        u64::from_str_radix(significant, 16).map_err(|_| "invalid hexadecimal significand")?;
    let zeroes = value.trailing_zeros();
    value >>= zeroes;
    let shift =
        4 * ((nonzero.len() - significant.len()) as i64 - fraction as i64) + i64::from(zeroes);
    let power = power
        .checked_add(shift)
        .ok_or("literal exponent is out of range")?;
    let width = 64 - value.leading_zeros();
    if width > 53 {
        return Err("hexadecimal literal is not exactly representable in binary64 (more than 53 significant bits)".into());
    }
    let highest = power
        .checked_add(i64::from(width) - 1)
        .ok_or("literal exponent is out of range")?;
    if highest > 1023 {
        return Err(
            "literal exceeds finite binary64; infinity requires the explicit bits form".into(),
        );
    }
    if power < -1074 {
        return Err(
            "literal is not exactly representable in binary64 (below the subnormal precision)"
                .into(),
        );
    }
    if highest >= -1022 {
        Ok(((highest + 1023) as u64) << 52 | ((value << (53 - width)) & FRACTION))
    } else {
        Ok(value << (power + 1074))
    }
}

// A nonnegative decimal value is coefficient * 10^power, with no leading or
// trailing coefficient zeroes (except zero itself). There is no large power
// allocation: even an enormous input exponent is just a bounded integer.
#[derive(PartialEq, Eq)]
struct Decimal {
    coefficient: String,
    power: i64,
}

impl Decimal {
    fn normalized(digits: &str, power: i64) -> Result<Self, String> {
        let digits = digits.trim_start_matches('0');
        if digits.is_empty() {
            return Ok(Self {
                coefficient: "0".into(),
                power: 0,
            });
        }
        let coefficient = digits.trim_end_matches('0');
        let power = power
            .checked_add((digits.len() - coefficient.len()) as i64)
            .ok_or("literal exponent is out of range")?;
        Ok(Self {
            coefficient: coefficient.into(),
            power,
        })
    }

    fn compare(&self, other: &Self) -> Ordering {
        match (self.coefficient == "0", other.coefficient == "0") {
            (true, true) => return Ordering::Equal,
            (true, false) => return Ordering::Less,
            (false, true) => return Ordering::Greater,
            _ => {}
        }
        let size = self.coefficient.len() as i128 + i128::from(self.power);
        let other_size = other.coefficient.len() as i128 + i128::from(other.power);
        size.cmp(&other_size).then_with(|| {
            let width = self.coefficient.len().max(other.coefficient.len());
            self.coefficient
                .bytes()
                .chain(std::iter::repeat(b'0'))
                .take(width)
                .cmp(
                    other
                        .coefficient
                        .bytes()
                        .chain(std::iter::repeat(b'0'))
                        .take(width),
                )
        })
    }
}

fn decimal_value(bits: u64) -> Decimal {
    let encoded_power = ((bits >> 52) & 2047) as i32;
    let significand = (bits & FRACTION) | if encoded_power == 0 { 0 } else { 1 << 52 };
    let power = if encoded_power == 0 {
        -1074
    } else {
        encoded_power - 1023 - 52
    };
    let mut digits: Vec<u8> = significand
        .to_string()
        .bytes()
        .rev()
        .map(|b| b - b'0')
        .collect();
    // M * 2^-k = M * 5^k * 10^-k. At most 1074 small-integer
    // multiplications and 768 decimal digits, independent of input exponent.
    let factor = if power < 0 { 5 } else { 2 };
    for _ in 0..power.unsigned_abs() {
        let mut carry = 0;
        for digit in &mut digits {
            let next = *digit * factor + carry;
            *digit = next % 10;
            carry = next / 10;
        }
        if carry != 0 {
            digits.push(carry);
        }
    }
    let coefficient: String = digits
        .into_iter()
        .rev()
        .map(|b| char::from(b + b'0'))
        .collect();
    Decimal::normalized(&coefficient, i64::from(power.min(0))).unwrap()
}

fn exact_spelling(bits: u64) -> String {
    let sign = if bits & SIGN == 0 { "" } else { "-" };
    let magnitude = bits & !SIGN;
    if magnitude == 0 || magnitude >> 52 == 2047 {
        return format!("f64_bits({bits})");
    }
    let encoded_power = magnitude >> 52;
    let power = if encoded_power == 0 {
        -1022
    } else {
        encoded_power as i64 - 1023
    };
    let leading = if encoded_power == 0 { '0' } else { '1' };
    let fraction = format!("{:013x}", magnitude & FRACTION);
    let fraction = fraction.trim_end_matches('0');
    let point = if fraction.is_empty() { "" } else { "." };
    format!("f64({sign}0x{leading}{point}{fraction}p{power})")
}

fn decimal_bits(text: &str, negative: bool) -> Result<u64, String> {
    let (significand, power) = match text.split_once(['e', 'E']) {
        Some((significand, power)) => (significand, exponent(power)?),
        None => (text, 0),
    };
    let (digits, fraction) = mantissa(significand, 10)?;
    let input = Decimal::normalized(
        &digits,
        power
            .checked_sub(fraction as i64)
            .ok_or("literal exponent is out of range")?,
    )?;
    if input.coefficient == "0" {
        return Ok(0);
    }
    let candidate = text
        .parse::<f64>()
        .map_err(|_| "invalid decimal binary64 payload")?;
    if !candidate.is_finite() {
        return Err(
            "literal exceeds finite binary64; infinity requires the explicit bits form".into(),
        );
    }
    let bits = candidate.to_bits();
    let actual = decimal_value(bits);
    match input.compare(&actual) {
        Ordering::Equal => Ok(bits),
        order => {
            let (lower, upper) = if order == Ordering::Less {
                (bits - 1, bits)
            } else {
                (bits, bits + 1)
            };
            let (lower, upper) = if negative {
                (upper | SIGN, lower | SIGN)
            } else {
                (lower, upper)
            };
            Err(format!(
                "decimal literal is not exactly representable in binary64; adjacent values are {} and {}; choose an exact hex or explicit bits payload",
                exact_spelling(lower),
                exact_spelling(upper)
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_hex_and_decimal_payloads_cover_binary64_boundaries() {
        for (text, expected) in [
            ("0", 0),
            ("1.5", 0x3ff8_0000_0000_0000),
            (".25", 0x3fd0_0000_0000_0000),
            ("3.", 0x4008_0000_0000_0000),
            ("125e-3", 0x3fc0_0000_0000_0000),
            ("9007199254740992", 0x4340_0000_0000_0000),
            ("0x1p-1074", 1),
            ("0x0.fffffffffffffp-1022", 0x000f_ffff_ffff_ffff),
            ("0x1p-1022", 0x0010_0000_0000_0000),
            ("0x1.fffffffffffffp1023", 0x7fef_ffff_ffff_ffff),
            ("0X18P-4", 0x3ff8_0000_0000_0000),
            ("0x20000000000002p-1", 0x4330_0000_0000_0001),
        ] {
            assert_eq!(bits(text, false).unwrap(), expected, "{text}");
            if expected != 0 {
                assert_eq!(bits(text, true).unwrap(), expected | SIGN, "-{text}");
            }
        }
        assert_eq!(
            bits(&format!("0x1{}p-4000", "0".repeat(1000)), false).unwrap(),
            1.0f64.to_bits()
        );
        assert_eq!(
            bits(&format!("1{}e-1000", "0".repeat(1000)), false).unwrap(),
            1.0f64.to_bits()
        );
    }

    #[test]
    fn rejects_rounding_nonfinite_and_implicit_signed_zero() {
        for text in [
            "0.1",
            "9007199254740993",
            "1e-9999",
            "1e9999",
            "0x1p-1075",
            "0x1p1024",
            "0x1.00000000000001p0",
            "0x3p-1075",
        ] {
            assert!(bits(text, false).is_err(), "{text}");
        }
        for text in ["0", "0.0", "0e9999", "0x0p-9999"] {
            assert!(bits(text, true).unwrap_err().contains("signed zero"));
        }
        for text in [
            "NaN",
            "inf",
            "1_000",
            "1f64",
            "0x1",
            "0x.p0",
            "1e",
            "1e+-2",
            "0x1p+",
            "0x1p9223372036854775808",
            "0x2p9223372036854775807",
        ] {
            assert!(bits(text, false).is_err(), "{text}");
        }
        let error = bits("0.1", false).unwrap_err();
        assert!(error.contains("f64(0x1.9999999999999p-4)"), "{error}");
        assert!(error.contains("f64(0x1.999999999999ap-4)"), "{error}");
    }

    #[test]
    fn exact_decimal_expansions_and_hex_spellings_round_trip_sampled_bits() {
        // Deterministic samples across the exponent range, including both
        // adjacent powers and subnormal edges; use the independent std hex-free
        // binary64 parser as well as the resource conversion.
        let mut sample = 0x1234_5678_9abc_def0u64;
        for exponent in [0, 1, 2, 1022, 1023, 1024, 2045, 2046]
            .into_iter()
            .chain((0..2047u64).step_by(31))
        {
            sample ^= sample << 13;
            sample ^= sample >> 7;
            sample ^= sample << 17;
            for fraction in [0, 1, FRACTION, sample & FRACTION] {
                let expected = exponent << 52 | fraction;
                let value = decimal_value(expected);
                let text = format!("{}e{}", value.coefficient, value.power);
                assert_eq!(text.parse::<f64>().unwrap().to_bits(), expected);
                assert_eq!(bits(&text, false).unwrap(), expected);
                if expected != 0 {
                    let hex = exact_spelling(expected);
                    assert_eq!(bits(&hex[4..hex.len() - 1], false).unwrap(), expected);
                }
            }
        }
    }
}
