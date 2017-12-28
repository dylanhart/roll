extern crate dice;
extern crate structopt;
#[macro_use] extern crate structopt_derive;

use dice::{Dice};
use structopt::{StructOpt};

#[derive(StructOpt, Debug)]
#[structopt(name = "roll", about = "compute dice rolls")]
struct Options {
    #[structopt(short = "r", long = "raw", help = "display results in raw format")]
    raw: bool,
    #[structopt(short = "c", long = "count", help = "number of times to roll", default_value = "1")]
    count: u32,
    #[structopt(help = "the dice roll")]
    dice: Dice,
}

fn main() {
    let opts = Options::from_args();
    for _ in 0 .. opts.count {
        let roll = opts.dice.roll();
        if !opts.raw {
            println!("{} = {} = {}", opts.dice, roll, roll.value());
        } else {
            println!("{}", roll.value());
        }
    }
}
