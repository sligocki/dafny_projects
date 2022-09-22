include "defs.dfy"

method ParseSymbol(symb_char : char) returns (symbol : Symbol) {
  if symb_char < '0' {
    return 0;  // Avoid
  } else {
    return (symb_char as int) - ('0' as int);
  }
}

method ParseState(state_char : char) returns (state : StateOrHalt) {
  if state_char >= 'H' || state_char < 'A' {
    return Halt;
  } else {
    return RunState((state_char as int) - ('A' as int));
  }
}

method ParseDir(dir_char : char) returns (dir : Dir) {
  match dir_char {
    case 'R' => return Right;
    case 'L' => return Left;
    case _   => return Right;  // Avoid
  }
}

method ParseTM(tm_str : string) returns (tm : TM) {
  var index := 0;
  var state := 0;
  tm := map[];
  while index + 2 < |tm_str|
    decreases |tm_str| - index
  {
    var symbol := 0;
    while index + 2 < |tm_str| && tm_str[index] != '_' {
      var new_symbol := ParseSymbol(tm_str[index]);
      var new_dir := ParseDir(tm_str[index+1]);
      var new_state := ParseState(tm_str[index+2]);
      var trans := Transition(new_symbol, new_dir, new_state);
      tm := tm[TransKey(state, symbol) := trans];
      index := index + 3;
      symbol := symbol + 1;
    }
    index := index + 1;
    state := state + 1;
  }

  return tm;
}