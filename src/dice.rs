#[macro_use] extern crate chomp;
extern crate itertools;
extern crate rand;

use itertools::{Itertools};
use rand::{thread_rng, Rng};
use std::fmt::{self, Display, Formatter};
use std::ops::{Add, Deref, Sub, Mul};
use std::str::{FromStr};

pub const D4: Dice = Dice::Die(4);
pub const D6: Dice = Dice::Die(6);
pub const D8: Dice = Dice::Die(8);
pub const D10: Dice = Dice::Die(10);
pub const D12: Dice = Dice::Die(12);
pub const D20: Dice = Dice::Die(20);

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Dice {
    Constant(u32),
    Die(u32),
    Repeat(u32, Box<Dice>, Option<Modifier>),
    Sum(Box<Dice>, Box<Dice>),
    Difference(Box<Dice>, Box<Dice>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Modifier {
    KeepHighest(u32),
    KeepLowest(u32),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Roll {
    Constant(u32),
    Die(i64),
    Repeat(Vec<ModifiedRoll>),
    Sum(Box<Roll>, Box<Roll>),
    Difference(Box<Roll>, Box<Roll>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModifiedRoll {
    status: RollStatus,
    roll: Roll,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RollStatus {
    Kept,
    Dropped,
}

impl Dice {
    pub fn from_constant(value: u32) -> Dice {
        Dice::Constant(value)
    }

    pub fn with_sides(sides: u32) -> Dice {
        Dice::Die(sides)
    }

    pub fn repeat(self, times: u32) -> Dice {
        Dice::Repeat(times, Box::new(self), None)
    }

    pub fn roll(&self) -> Roll {
        match *self {
            Dice::Constant(n) => Roll::Constant(n),
            Dice::Die(n) => Roll::Die(thread_rng().gen_range(1, (n as i64)+1)),
            Dice::Repeat(n, ref dice, modifier) => {
                let rolls = (0..n).into_iter().map(|_| dice.roll());

                let modded_rolls = match modifier {
                    Some(Modifier::KeepHighest(count)) => {
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
                    Some(Modifier::KeepLowest(count)) => {
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
                    None => rolls.map(|r| ModifiedRoll { status: RollStatus::Kept, roll: r }).collect()
                };

                Roll::Repeat(modded_rolls)
            },
            Dice::Sum(ref a, ref b) => Roll::Sum(Box::new(a.roll()), Box::new(b.roll())),
            Dice::Difference(ref a, ref b) => Roll::Difference(Box::new(a.roll()), Box::new(b.roll())),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ParseError {
    InvalidInput,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            ParseError::InvalidInput => write!(f, "could not parse dice roll"),
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

impl Roll {
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

    trait CharInput: Input<Token=char> {}
    impl<T: Input<Token=char>> CharInput for T {}

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

    fn spaces<I: CharInput>(input: I) -> SimpleResult<I, I::Buffer> {
        parse!{ input;
            take_while(|ch| ch == ' ');
        }
    }

    fn number<I: CharInput>(input: I) -> SimpleResult<I, u32> {
        parse! { input;
            let chars = take_while1(|c| c >= '0' && c <= '9');
            ret chars.fold(0, |acc, ch| 10*acc + (ch as u8 - b'0') as u32);
        }
    }

    fn constant<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let n = number();
            ret Dice::Constant(n);
        }
    }

    fn die<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            token('d');
            let n = number();
            ret Dice::Die(n);
        }
    }

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

    fn repeat<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let n = number();
            let d = or(die, term);
            let m = opt(|i| modifier(i, n));
            ret Dice::Repeat(n, Box::new(d), m);
        }
    }

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

    fn dice<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            let d = sum() <|> diff() <|> repeat() <|> term() <|> die() <|> constant();
            ret d;
        }
    }

    fn untrimmed_dice<I: CharInput>(input: I) -> SimpleResult<I, Dice> {
        parse!{ input;
            spaces();
            let d = dice();
            spaces();
            eof();
            ret d;
        }
    }

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
        assert_eq!(Dice::from_str("d20"), Ok(D20));
        assert_eq!(Dice::from_str("3d6"), Ok(3 * D6));
        assert_eq!(Dice::from_str("   (( 3d6  )    ) "), Ok(3 * D6));
        assert_eq!(Dice::from_str("d12 + 4"), Ok(D12 + 4));
        assert_eq!(Dice::from_str("2d8 + 5"), Ok(2*D8 + 5));
        assert_eq!(Dice::from_str("(2d8 + 5) - 3"), Ok(2*D8 + 5 - 3));
        assert_eq!(Dice::from_str("3(2d8 + 5)"), Ok(3*(2*D8 + 5)));
        assert_eq!(Dice::from_str("2d20d6"), Err(()));
    }
}
