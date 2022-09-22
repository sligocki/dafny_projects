include "impl.dfy"
include "parse.dfy"

function method StateToString(state : StateOrHalt) : string {
  match state {
    case Halt => "Halt"
    case RunState(state) => 
      if state < 20
        then [(state as char) + 'A']
        else "?"
  }
}

function method DirToString(dir : Dir) : string {
  match dir {
    case Left => "L"
    case Right => "R"
  }
}

method PrintConfig(config : Config) {
  print config.step_num,
        " State: ", StateToString(config.state),
        " Symbol: ", ReadTape(config.tape, config.pos),
        " Pos: ", config.pos, "\n";
}

method VerboseSimTM(tm_str : string, num_steps : nat) {
  var tm := ParseTM(tm_str);
  var i := 0;
  var config := InitConfig;
  while i < num_steps && !config.state.Halt?
    invariant 0 <= i <= num_steps
    decreases num_steps - i
  {
    var cur_symbol := ReadTape(config.tape, config.pos);
    var trans := LookupTrans(tm, config.state.state, cur_symbol);
    print StateToString(config.state), cur_symbol, "->", trans.symbol, DirToString(trans.dir), StateToString(trans.state), "\n";
    config := Step(tm, config);
    PrintConfig(config);
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, num_steps : nat) {
  var tm := ParseTM(tm_str);
  var config := RunTM(tm, InitConfig, num_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  VerboseSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 108);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000_000);
}