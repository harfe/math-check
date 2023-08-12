use super::constants;
use super::context;
use super::reader::Reader;
use super::terms::Tm;
use super::terms::Ty;
use context::Context;
use std::error;
use std::fmt;

// type Tm = usize;
// type Ty = usize;
// type Thm = usize;

pub type BoxRes<T> = Result<T, Box<MyError>>;

#[derive(Debug)]
pub struct MyError {
    expect: String,
    got: String,
    line: u32,
    column: u32,
    err_code: ErrCode,
}

#[derive(Debug, PartialEq)]
pub enum ErrCode {
    NoArgs,
    TwoArgs,
    FileRead,
    Impossible,
    //   NotImplemented,
    Ascii,
    AsciiCtrl,
    Expected,
    ExpectedType,
    ForallMatch,
    //   FunapMatch,
    UsedWord,
    UnknownVar,
    UnknownThm,
    UnknownWord,
    ProveMatch,
    ImpMatch,
    MpMatch,
}

impl MyError {
    pub fn new(err_code: ErrCode) -> Box<MyError> {
        //     panic!("error");
        Box::new(MyError {
            expect: "".to_string(),
            got: "".to_string(),
            line: 0,
            column: 0,
            err_code: err_code,
        })
    }

    pub fn set_got_term_with_type(&mut self, tm: Tm, c: &Context) {
        if let Err(_) = self.set_got_term_with_type_2(tm, c) {
            self.err_code = ErrCode::Impossible;
        }
    }

    fn set_got_term_with_type_2(&mut self, tm: Tm, c: &Context) -> BoxRes<()> {
        let ty: Ty = c.terms.get_type(tm)?;
        let tm_str = c.print_term(tm)?;
        let ty_str = c.print_type(ty)?;
        self.got = format!("`{}`\nhas type `{}`", tm_str, ty_str);
        Ok(())
    }

    pub fn set_expect(&mut self, exp: &str) {
        self.expect = exp.to_string();
    }

    pub fn set_got(&mut self, g: &str) {
        self.got = g.to_string();
    }

    pub fn set_location_pair(&mut self, (a, b): (u32, u32)) {
        self.line = a;
        self.column = b;
    }

    pub fn set_location_from_reader(&mut self, r: &Reader) {
        self.set_location_pair(r.location());
    }

    pub fn set_last_location_from_reader(&mut self, r: &Reader) {
        self.set_location_pair(r.last_location());
    }

    pub fn output(&self) -> String {
        //     code2msg(&self.err_code)
        let mut out = if show_location(&self.err_code) {
            format!("line {}, column {}: ", self.line, self.column)
        } else {
            "Error: ".to_string()
        };
        match &self.err_code {
            ErrCode::Expected => {
                out.push_str("Expected ");
                out.push_str(&self.expect);
                out.push_str(", got ");
                out.push_str(&self.got);
                out.push_str(" instead.");
            }
            ErrCode::ExpectedType => {
                out.push_str("Expected something of type `");
                out.push_str(&self.expect);
                out.push_str("`, but\n");
                out.push_str(&self.got);
                out.push_str(".");
            }
            ErrCode::NoArgs => {
                out.push_str("No arguments given.");
            }
            ErrCode::TwoArgs => {
                out.push_str("More than one argument given.");
            }
            ErrCode::FileRead => {
                out.push_str("Could not read file.");
            }
            ErrCode::Impossible => {
                out.push_str("This should be impossible.");
            }
            ErrCode::Ascii => {
                out.push_str("Only ASCII characters are allowed.");
            }
            ErrCode::ForallMatch => {
                out.push_str(&format!(
                    "Could not match with `{} {} {} {}` in theorem `{}`.",
                    constants::FUNAP,
                    constants::FORALL,
                    constants::WILDCARD,
                    constants::WILDCARD,
                    &self.got,
                ));
            }
            //       ErrCode::FunapMatch => {
            //         out.push_str("Could not match with `");
            //         out.push_str(constants::FUNAP);
            //         out.push_str("`.");
            //       }
            ErrCode::ImpMatch => {
                out.push_str(&format!(
                    "Could not match with `{} {} {} {} {}` in theorem `{}`",
                    constants::FUNAP,
                    constants::IMP,
                    constants::PAIR,
                    constants::WILDCARD,
                    constants::WILDCARD,
                    &self.got
                ));
            }
            ErrCode::MpMatch => {
                //         out.push_str(constants::MP);
                //         out.push_str(": second theorem does not match");
                out.push_str(&format!(
                    "{}: second theorem \n`{}`\n{}\n`{}`\n{}",
                    constants::MP,
                    &self.got,
                    "does not match the term",
                    &self.expect,
                    "which is the consequent of the first theorem."
                ));
            }
            ErrCode::AsciiCtrl => {
                out.push_str(
                    "No control characters other than \
           newline or tab are allowed.",
                );
            }
            ErrCode::UsedWord => {
                out.push_str("word \"");
                out.push_str(&self.got);
                out.push_str("\" already used.");
            }
            ErrCode::UnknownVar => {
                out.push_str("variable `");
                out.push_str(&self.got);
                out.push_str("` unknown.");
            }
            ErrCode::UnknownThm => {
                out.push_str("theorem '");
                out.push_str(&self.got);
                out.push_str("' unknown.");
            }
            ErrCode::UnknownWord => {
                out.push_str("word \"");
                out.push_str(&self.got);
                out.push_str("\" unknown.");
            }
            ErrCode::ProveMatch => {
                out.push_str(&format!(
                    "{}: could not match term\n`{}`\nwith theorem\n`{}`.",
                    constants::PROVE,
                    &self.expect,
                    &self.got,
                ));
            }
        };
        out
    }

    pub fn exit_code(&self) -> i32 {
        match self.err_code {
            ErrCode::NoArgs => 2,
            ErrCode::TwoArgs => 3,
            ErrCode::FileRead => 4,
            ErrCode::Impossible => 5,
            ErrCode::Ascii => 6,
            ErrCode::AsciiCtrl => 6,
            _ => 1,
        }
    }

    #[cfg(test)]
    pub fn has_error(&self, ec: ErrCode) -> bool {
        self.err_code == ec
    }
}

fn show_location(ec: &ErrCode) -> bool {
    match ec {
        ErrCode::NoArgs => false,
        ErrCode::TwoArgs => false,
        ErrCode::FileRead => false,
        _ => true,
    }
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.output())
    }
}

impl error::Error for MyError {
    //   fn description(&self)
}

pub fn opt2imposs<T>(o: Option<T>) -> BoxRes<T> {
    match o {
        Some(x) => Ok(x),
        None => Err(MyError::new(ErrCode::Impossible)),
    }
}

pub fn some2imposs<T>(o: Option<T>) -> BoxRes<()> {
    match o {
        Some(_) => Err(MyError::new(ErrCode::Impossible)),
        None => Ok(()),
    }
}

pub fn boxres2imposs<T>(br: BoxRes<T>) -> BoxRes<T> {
    match br {
        Err(_) => Err(MyError::new(ErrCode::Impossible)),
        Ok(x) => Ok(x),
    }
}

pub fn expected<T: std::cmp::PartialEq>(expected: T, val: T) -> BoxRes<()> {
    if expected == val {
        Ok(())
    } else {
        Err(MyError::new(ErrCode::Impossible))
    }
}

pub fn add_loc<T>(br: BoxRes<T>, loc: (u32, u32)) -> BoxRes<T> {
    match br {
        Ok(x) => Ok(x),
        Err(mut e) => {
            e.set_location_pair(loc);
            Err(e)
        }
    }
}
