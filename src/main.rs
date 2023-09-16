use std::env;
use std::process;

mod min;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 3 {
        eprintln!("Please provide exactly two arguments.");
        process::exit(1);
    }

    let num1 = args[1].parse::<i32>().unwrap_or_else(|_| {
        eprintln!("Error reading the first number.");
        process::exit(1);
    });

    let num2 = args[2].parse::<i32>().unwrap_or_else(|_| {
        eprintln!("Error reading the second number.");
        process::exit(1);
    });

    println!("The minimum of {} and {} is {}", num1, num2, min::min(num1, num2));
}
