extern crate dice;
extern crate structopt;
#[macro_use] extern crate structopt_derive;

use dice::{Dice};
use structopt::{StructOpt};

#[derive(StructOpt, Debug)]
#[structopt(name = "roll", about = "compute dice rolls")]
struct Options {
    #[structopt(help = "dice values to roll")]
    rolls: Vec<Dice>,
}

fn main() {
    let opts = Options::from_args();

    for roll in opts.rolls.iter() {
        println!("{} = {}", roll, roll.roll());
    }
}
