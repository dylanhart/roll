extern crate dice;
extern crate structopt;
#[macro_use] extern crate structopt_derive;

use dice::{Dice};
use structopt::{StructOpt};

#[derive(StructOpt, Debug)]
#[structopt(name = "roll", about = "compute dice rolls")]
struct Options {
    #[structopt(help = "dice values to roll")]
    dice: Vec<Dice>,
}

fn main() {
    let opts = Options::from_args();

    for dice in opts.dice.iter() {
        let roll = dice.roll();
        println!("{} = {} = {}", dice, roll, roll.value());
    }
}
