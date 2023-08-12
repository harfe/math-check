// TODO
// rewrite match_internal with a better algorithm
// rename keyword -> reserved word (or something like it)
// reduce pub
// can we get rid of Theorem(),TheoremType() variant?
//   - careful with non-unique numbers!
//   - also abolish is_thm()
// use more myerr::expected
// check all the logic for match_internal again !
// do tests with printing and parsing again
// more methods, less functions
// research design considerations for singletons
// reduce code/complexity
// improve performance
// add some standard axioms before parsing?
// add include command?
// use extra file for types?
// end TODO list

mod myerr;
use myerr::BoxRes;
use myerr::ErrCode;
use myerr::MyError;
mod reader;
use reader::Reader;
mod constants;
mod context;
mod names;
mod terms;
// mod types;
mod parse;
// mod term;
// mod theorem;

fn get_filename_from_args() -> BoxRes<String> {
    let mut args = std::env::args().skip(1);
    let filename: String = match args.next() {
        None => {
            return Err(MyError::new(ErrCode::NoArgs));
        }
        Some(x) => x,
    };
    match args.next() {
        Some(_) => {
            return Err(MyError::new(ErrCode::TwoArgs));
        }
        None => (),
    };
    Ok(filename)
}

fn main2() -> BoxRes<()> {
    // gets called by main only, parses args and file
    let filename: String = get_filename_from_args()?;
    let content: String = match std::fs::read_to_string(&filename) {
        Err(_) => {
            return Err(MyError::new(ErrCode::FileRead));
        }
        Ok(t) => t,
    };
    let mut r: Reader = Reader::new(&content);
    parse::parse_file(&mut r)?;
    Ok(())
}

fn main() {
    if let Err(x) = main2() {
        println!("{}", x.output());
        std::process::exit(x.exit_code())
    }
    println!("done. No Errors found.");
}

#[test]
fn test_report_type_sizes() {
    assert_eq!(12, std::mem::size_of::<terms::TermEntry>());
    assert_eq!(12, std::mem::size_of::<terms::TypeEntry>());
    assert_eq!(48, std::mem::size_of::<terms::Terms>());
    //   assert_eq!(224, std::mem::size_of::<terms::MatchHelper>());
    assert_eq!(24, std::mem::size_of::<String>());
    assert_eq!(64, std::mem::size_of::<myerr::MyError>());
    assert_eq!(16, std::mem::size_of::<BoxRes<terms::TermEntry>>());
    assert_eq!(16, std::mem::size_of::<BoxRes<terms::TmOrThm>>());
    assert_eq!(8, std::mem::size_of::<terms::TmOrThm>());
    assert_eq!(4, std::mem::size_of::<terms::Tm>());
    assert_eq!(8, std::mem::size_of::<usize>());
}
