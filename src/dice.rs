#![deny(missing_docs)]

//! A library to parse dice expressions and roll dice.
//!
//! ## Usage
//!
//! Create expressions in code:
//!
//! ```rust
//! # use dice::*;
//! let dice = 3 * D6 + 4;
//! assert_eq!(dice.to_string(), "3d6 + 4")
//! ```
//!
//! Parse dice expressions from strings:
//!
//! ```rust
//! # use dice::*;
//! let dice = Dice::parse("d20 + 7").unwrap();
//! assert_eq!(dice, D20 + 7);
//! ```
//!
//! Compute dice rolls:
//!
//! ```rust
//! # use dice::*;
//! let dice = D20 + 12;
//! let roll = dice.roll();
//! let value = roll.value();
//! println!("{} = {} = {}", dice, roll, value);
//! ```

#[macro_use] extern crate chomp;
extern crate itertools;
extern crate rand;

use itertools::{Itertools};
use rand::{thread_rng, Rng};
use std::fmt::{self, Display, Formatter};
use std::ops::{Add, Deref, Sub, Mul};
use std::str::{FromStr};

/// A four sided die
pub const D4: Dice = Dice::Die(4);
/// A six sided die
pub const D6: Dice = Dice::Die(6);
/// A eight sided die
pub const D8: Dice = Dice::Die(8);
/// A ten sided die
pub const D10: Dice = Dice::Die(10);
/// A twelve sided die
pub const D12: Dice = Dice::Die(12);
/// A twenty sided die
pub const D20: Dice = Dice::Die(20);

/// A set of dice that can be rolled
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Dice {
    /// a constant value
    Constant(u32),
    /// an `n` sided die
    Die(u32),
    /// a repeated set of dice with an optional modifier
    Repeat(u32, Box<Dice>, Option<Modifier>),
    /// the sum of two sets of dice
    Sum(Box<Dice>, Box<Dice>),
    /// the difference of two sets of dice
    Difference(Box<Dice>, Box<Dice>),
}

/// Modifiers for repeated dice
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Modifier {
    /// keep the `n` highest valued dice
    KeepHighest(u32),
    /// keep the `n` lowest valued dice
    KeepLowest(u32),
}

/// An error encountered while parsing a dice expression
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ParseError {
    /// The given input is invalid
    InvalidInput,
}

/// The result of rolling dice
///
/// The structure of a `Roll` will match the structure of the `Dice` that rolled it and will contain
/// the generated values.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Roll {
    /// a constant value
    Constant(u32),
    /// a result of a die roll
    Die(i64),
    /// a set of rolls with modified statuses
    Repeat(Vec<ModifiedRoll>),
    /// a sum of two rolls
    Sum(Box<Roll>, Box<Roll>),
    /// a difference of two rolls
    Difference(Box<Roll>, Box<Roll>),
}

/// A modified `Roll` with a `RollStatus`
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModifiedRoll {
    /// The status of this `Roll`
    status: RollStatus,
    /// The modified `Roll`
    roll: Roll,
}

/// A status for a `ModifiedRoll`
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RollStatus {
    /// The roll is kept as normal
    Kept,
    /// The roll is dropped and is not calculated towards the final value
    Dropped,
}

impl Dice {
    /// Create a dice from the given expression
    pub fn parse(expression: &str) -> Result<Dice, ParseError> {
        Dice::from_str(expression)
    }

    /// Create a `Dice` from a constant `value`
    pub fn from_constant(value: u32) -> Dice {
        Dice::Constant(value)
    }

    /// Create a `Dice` from a die with the given number of `sides`
    pub fn with_sides(sides: u32) -> Dice {
        Dice::Die(sides)
    }

    /// Creates a new set of `Dice` by repeating this set of dice a given number of `times`
    pub fn repeat(self, times: u32) -> Dice {
        Dice::Repeat(times, Box::new(self), None)
    }

    /// Creates a new set of `Dice` by repeating this set of dice a given number of `times` with the
    /// given `modifier`
    pub fn repeat_with_modifier(self, times: u32, modifier: Modifier) -> Dice {
        Dice::Repeat(times, Box::new(self), Some(modifier))
    }

    /// Performs a dice roll from this set of `Dice` using the default random number generator
    pub fn roll(&self) -> Roll {
        self.roll_with_rng(&mut thread_rng())
    }

    /// Performs a dice roll from this set of `Dice` using the given random number generator
    pub fn roll_with_rng<R: Rng>(&self, rng: &mut R) -> Roll {
        match *self {
            Dice::Constant(n) => Roll::Constant(n),
            Dice::Die(n) => Roll::Die(rng.gen_range(1, (n as i64)+1)),
            Dice::Repeat(n, ref dice, modifier) => {
                let rolls = (0..n).into_iter().map(|_| dice.roll());

                let modded_rolls = match modifier {
                    Some(Modifier::KeepHighest(count)) => {
                        let ordered = rolls.sorted_by(|a, b| Ord::cmp(&b.value(), &a.value()));
                        ordered.into_iter().enumerate()
                            .map(|(i, r)| {
                                let count = count as usize;
                                ModifiedRoll {
                                    status: if i < count { RollStatus::Kept } else { RollStatus::Dropped },
                                    roll: r
                                }
                            })
                            .collect()
                    },
                    Some(Modifier::KeepLowest(count)) => {
                        let ordered = rolls.sorted_by(|a, b| Ord::cmp(&a.value(), &b.value()));
                        ordered.into_iter().enumerate()
                            .map(|(i, r)| {
                                let count = count as usize;
                                ModifiedRoll {
                                    status: if i < count { RollStatus::Kept } else { RollStatus::Dropped },
                                    roll: r
                                }
                            })
                            .collect()
                    },
                    None => rolls.map(|r| ModifiedRoll { status: RollStatus::Kept, roll: r }).collect()
                };

                Roll::Repeat(modded_rolls)
            },
            Dice::Sum(ref a, ref b) => Roll::Sum(Box::new(a.roll()), Box::new(b.roll())),
            Dice::Difference(ref a, ref b) => Roll::Difference(Box::new(a.roll()), Box::new(b.roll())),
        }
    }
}

impl FromStr for Dice {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parser::parse_dice(s).ok_or(ParseError::InvalidInput)
    }
}

impl Display for Dice {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Dice::Constant(n) => write!(f, "{}", n),
            Dice::Die(n) => write!(f, "d{}", n),
            Dice::Repeat(n, ref dice, None) => {
                if let &Dice::Die(sides) = dice.deref() {
                    write!(f, "{}d{}", n, sides)
                } else {
                    write!(f, "{}({})", n, dice)
                }
            },
            Dice::Repeat(n, ref dice, Some(modifier)) => {
                if let &Dice::Die(sides) = dice.deref() {
                    write!(f, "{}d{}{}", n, sides, modifier)
                } else {
                    write!(f, "{}({}){}", n, dice, modifier)
                }
            },
            Dice::Sum(ref a, ref b) => write!(f, "{} + {}", a, b),
            Dice::Difference(ref a, ref b) => write!(f, "{} - {}", a, b),
        }
    }
}

impl Mul<Dice> for u32 {
    type Output = Dice;
    fn mul(self, rhs: Dice) -> Self::Output {
        rhs.repeat(self)
    }
}

impl Mul<u32> for Dice {
    type Output = Dice;
    fn mul(self, rhs: u32) -> Self::Output {
        self.repeat(rhs)
    }
}

impl Add<Dice> for Dice {
    type Output = Dice;
    fn add(self, rhs: Dice) -> Self::Output {
        Dice::Sum(Box::new(self), Box::new(rhs))
    }
}

impl Add<u32> for Dice {
    type Output = Dice;
    fn add(self, rhs: u32) -> Self::Output {
        Dice::Sum(Box::new(self), Box::new(Dice::Constant(rhs)))
    }
}

impl Add<Dice> for u32 {
    type Output = Dice;
    fn add(self, rhs: Dice) -> Self::Output {
        Dice::Sum(Box::new(rhs), Box::new(Dice::Constant(self)))
    }
}

impl Sub<Dice> for Dice {
    type Output = Dice;
    fn sub(self, rhs: Dice) -> Self::Output {
        Dice::Difference(Box::new(self), Box::new(rhs))
    }
}

impl Sub<u32> for Dice {
    type Output = Dice;
    fn sub(self, rhs: u32) -> Self::Output {
        Dice::Difference(Box::new(self), Box::new(Dice::Constant(rhs)))
    }
}

impl Sub<Dice> for u32 {
    type Output = Dice;
    fn sub(self, rhs: Dice) -> Self::Output {
        Dice::Difference(Box::new(rhs), Box::new(Dice::Constant(self)))
    }
}

impl Display for Modifier {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Modifier::KeepHighest(n) => write!(f, "h{}", n),
            Modifier::KeepLowest(n) => write!(f, "l{}", n),
        }
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            ParseError::InvalidInput => write!(f, "could not parse dice roll"),
        }
    }
}

impl Roll {
    /// Compute the integer value of the roll
    pub fn value(&self) -> i64 {
        match *self {
            Roll::Constant(n) => n as i64,
            Roll::Die(val) => val,
            Roll::Repeat(ref rolls) => rolls.iter().map(ModifiedRoll::value).sum(),
            Roll::Sum(ref a, ref b) => a.value() + b.value(),
            Roll::Difference(ref a, ref b) => a.value() - b.value(),
        }
    }
}

impl Display for Roll {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Roll::Constant(n) => write!(f, "{}", n),
            Roll::Die(val) => write!(f, "{}", val),
            Roll::Repeat(ref rolls) => {
                let mut res = write!(f, "[");

                let mut iter = rolls.iter();

                if let Some(roll) = iter.next() {
                    res = res.and_then(|_| write!(f, "{}", roll));
                }

                for roll in iter {
                    res = res.and_then(|_| write!(f, " + {}", roll));
                }

                res.and_then(|_| write!(f, "]"))
            },
            Roll::Sum(ref a, ref b) => write!(f, "{} + {}", a, b),
            Roll::Difference(ref a, ref b) => write!(f, "{} - {}", a, b),
        }
    }
}

impl ModifiedRoll {
    /// Compute the modified integer value of the roll
    fn value(&self) -> i64 {
        match self.status {
            RollStatus::Kept => self.roll.value(),
            RollStatus::Dropped => 0,
        }
    }
}

impl Display for ModifiedRoll {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let extra = match self.status {
            RollStatus::Kept => "",
            RollStatus::Dropped => "<dropped>",
        };

        match self.roll {
            Roll::Sum(..) | Roll::Difference(..) => {
                write!(f, "({}){}", self.roll, extra)
            },
            _ => {
                write!(f, "{}{}", self.roll, extra)
            },
        }
    }
}

mod parser {
    use super::*;
    use chomp::prelude::*;

    /// The character based input that will be used
    trait CharInput: Input<Token=char> {}
    impl<T: Input<Token=char>> CharInput for T {}

    /// A combinator to produce an `Option`
    fn opt<I: Input, U, F>(input: I, mut parser: F) -> SimpleResult<I, Option<U>>
    where F: FnMut(I) -> SimpleResult<I, U>
    {
        use chomp::primitives::{Primitives, IntoInner};

        let start = input.mark();

        match parser(input).into_inner() {
            (i, Ok(value)) => i.ret(Some(value)),
            (i, Err(_)) => i.restore(start).ret(None),
        }
    }

    /// Zero or more spaces
    fn spaces<I: CharInput>(input: I) -> SimpleResult<I, I::Buffer> {
        parse!{ input;
            take_while(|ch| ch == ' ');
        }
    }

    /// An unsigned integer
    fn number<I: CharInput>(input: I) -> SimpleResult<I, u32> {
        parse! { input;
            let chars = take_while1(|c| c >= '0' && c <= '9');
            ret chars.fold(0, |acc, ch| 10*acc + (ch as u8 - b'0') as u32);
        }
    }

    /// A constant `Dice`
    fn constant<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let n = number();
            ret Dice::Constant(n);
        }
    }

    /// A single die
    fn die<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            token('d');
            let n = number();
            ret Dice::Die(n);
        }
    }

    /// A set of `Dice` wrapped in parenthesis
    fn term<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            token('(');
            spaces();
            let d = dice();
            spaces();
            token(')');
            ret d;
        }
    }

    /// A `Modifier` suffix
    fn modifier<I: CharInput>(input: I, repeat_count: u32) -> SimpleResult<I, Modifier> {
        let keep_high = |i: I| {
            parse!{ i;
                token('h');
                let n = opt(number);
                ret Modifier::KeepHighest(n.unwrap_or(repeat_count-1));
            }
        };
        let keep_low = |i: I| {
            parse!{ i;
                token('l');
                let n = opt(number);
                ret Modifier::KeepLowest(n.unwrap_or(repeat_count-1));
            }
        };
        parse!{ input;
            keep_high() <|> keep_low()
        }
    }

    /// A repeated set of `Dice` with an optional `Modifier`
    fn repeat<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let n = number();
            let d = or(die, term);
            let m = opt(|i| modifier(i, n));
            ret Dice::Repeat(n, Box::new(d), m);
        }
    }

    /// A sum of two sets of `Dice`
    fn sum<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let a = repeat() <|> term() <|> die() <|> constant();
            spaces();
            token('+');
            spaces();
            let b = dice();
            ret a + b;
        }
    }

    /// A difference of two sets of `Dice`
    fn diff<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let a = repeat() <|> term() <|> die() <|> constant();
            spaces();
            token('-');
            spaces();
            let b = dice();
            ret a - b;
        }
    }

    /// A set of `Dice`
    fn dice<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let d = sum() <|> diff() <|> repeat() <|> term() <|> die() <|> constant();
            ret d;
        }
    }

    /// A set of `Dice` surrounded with whitespace ending with EOF
    fn untrimmed_dice<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            spaces();
            let d = dice();
            spaces();
            eof();
            ret d;
        }
    }

    /// Parse a given dice expression into a set of `Dice`. Returns `None` if the expression is
    /// invalid.
    pub fn parse_dice(text: &str) -> Option<Dice> {
        parse_only_str(untrimmed_dice, text).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_string() {
        assert_eq!("d20", D20.to_string());
        assert_eq!("3d6", (3 * D6).to_string());
        assert_eq!("3d6", (D6 * 3).to_string());
        assert_eq!("d12 + 4", (D12 + 4).to_string());
        assert_eq!("2d8 + 5", (2*D8 + 5).to_string());
        assert_eq!("2d8 + 5 - 3", (2*D8 + 5 - 3).to_string());
        assert_eq!("3(2d8 + 5)", (3*(2*D8 + 5)).to_string());
    }

    #[test]
    fn test_from_string() {
        assert_eq!(Dice::parse("d20"), Ok(D20));
        assert_eq!(Dice::parse("3d6"), Ok(3 * D6));
        assert_eq!(Dice::parse("   (( 3d6  )    ) "), Ok(3 * D6));
        assert_eq!(Dice::parse("d12 + 4"), Ok(D12 + 4));
        assert_eq!(Dice::parse("2d8 + 5"), Ok(2*D8 + 5));
        assert_eq!(Dice::parse("(2d8 + 5) - 3"), Ok(2*D8 + 5 - 3));
        assert_eq!(Dice::parse("3(2d8 + 5)"), Ok(3*(2*D8 + 5)));
        assert_eq!(Dice::parse("2d20d6"), Err(ParseError::InvalidInput));
    }
}
