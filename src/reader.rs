use super::myerr;
use super::BoxRes;
use super::ErrCode;
use super::MyError;
use std::str::Chars;

pub struct Reader<'a> {
    cs: Chars<'a>,
    linenum: u32,
    last_linenum: u32,
    colnum: u32,
    last_colnum: u32,
    loc_stack: Vec<(u32, u32)>,
}

impl<'b> Reader<'b> {
    pub fn new<'c>(f: &'c str) -> Reader<'c> {
        Reader {
            cs: f.chars(),
            linenum: 1,
            last_linenum: 1,
            colnum: 1,
            last_colnum: 0,
            loc_stack: Vec::new(),
        }
    }

    fn word(&mut self) -> BoxRes<String> {
        match self.word_internal() {
            Ok(x) => {
                if "" == x {
                    let mut e = MyError::new(ErrCode::Expected);
                    e.set_got("end of file");
                    e.set_location_from_reader(self);
                    Err(e)
                } else {
                    Ok(x)
                }
            }
            Err(e) => Err(e),
        }
    }

    pub fn word_exp(&mut self, exp: &str) -> BoxRes<String> {
        match self.word() {
            Ok(x) => Ok(x),
            Err(mut e) => {
                e.set_expect(exp);
                Err(e)
            }
        }
    }

    pub fn confirm_eof(&mut self) -> BoxRes<()> {
        match self.word_internal() {
            Ok(x) => {
                if "" == x {
                    Ok(())
                } else {
                    let mut e = MyError::new(ErrCode::Expected);
                    e.set_expect("end of file");
                    e.set_got(&format!("\"{}\"", x));
                    e.set_last_location_from_reader(self);
                    Err(e)
                }
            }
            Err(x) => Err(x),
        }
    }

    fn word_internal(&mut self) -> BoxRes<String> {
        let mut ret = String::new();
        let mut is_comment: bool = false;
        let mut last_whitespace: bool = true;
        loop {
            let mut is_whitespace: bool = false;
            let nextchar: char = match self.cs.next() {
                None => {
                    break;
                }
                Some('\n') => {
                    is_whitespace = true;
                    is_comment = false;
                    self.linenum += 1;
                    self.colnum = 0;
                    ' '
                }
                Some('#') => {
                    is_comment = last_whitespace;
                    '#'
                }
                Some(' ') | Some('\t') => {
                    is_whitespace = true;
                    ' '
                }
                Some(x) if !x.is_ascii() => {
                    let mut e = MyError::new(ErrCode::Ascii);
                    e.set_location_from_reader(self);
                    return Err(e);
                }
                Some(x) if x.is_ascii_control() => {
                    let mut e = MyError::new(ErrCode::AsciiCtrl);
                    e.set_location_from_reader(self);
                    return Err(e);
                }
                Some(x) => x,
            };
            self.colnum += 1;
            if is_comment {
                continue;
            }
            if is_whitespace {
                if !last_whitespace {
                    break; // finish word
                }
                continue; // continue looking for non-whitespace
            } else {
                if last_whitespace {
                    self.last_linenum = self.linenum;
                    self.last_colnum = self.colnum - 1;
                    last_whitespace = false;
                }
            }
            ret.push(nextchar);
        }
        Ok(ret)
    }

    pub fn last_location(&self) -> (u32, u32) {
        (self.last_linenum, self.last_colnum)
    }

    pub fn location(&self) -> (u32, u32) {
        (self.linenum, self.colnum)
    }

    pub fn add_last_loc<T>(&self, br: BoxRes<T>) -> BoxRes<T> {
        // adds last location to error, if error
        myerr::add_loc(br, self.last_location())
    }

    pub fn loc_push(&mut self) {
        let x = (self.last_linenum, self.last_colnum);
        self.loc_stack.push(x);
    }

    pub fn loc_pop(&mut self) -> BoxRes<(u32, u32)> {
        match self.loc_stack.pop() {
            Some(x) => Ok(x),
            None => Err(MyError::new(ErrCode::Impossible)),
        }
    }

    pub fn confirm_empty_loc_stack(&self) -> BoxRes<()> {
        if self.loc_stack.is_empty() {
            Ok(())
        } else {
            Err(MyError::new(ErrCode::Impossible))
        }
    }

    //   pub fn clear_loc_stack(&mut self) {
    //     self.loc_stack.clear();
    //   }
}

#[test]
fn test_reader() {
    let t = "this is a\n".to_string();
    let t = t + "\t\ttest.\n\n";
    let t = t + "#comment some\n and thi#s    i#s\n";
    let t = t + "not commented    # but this is  \n\n";
    let mut r = Reader::new(&t);
    let w = r.word().expect("test");
    assert_eq!("this".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("is".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("a".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("test.".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("and".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("thi#s".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("i#s".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("not".to_string(), w);
    let w = r.word().expect("test");
    assert_eq!("commented".to_string(), w);
    r.confirm_eof().expect("test");
}
