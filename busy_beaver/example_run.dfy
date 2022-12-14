include "impl.dfy"
include "parse.dfy"

method PrintConfig(config : Config) {
  var score := ScoreTape(config.tape);
  print "Steps: ", config.step_num, " Score: ", score,
        " State: ", Parse.StateToString(config.state), " Pos: ", config.pos, "\n";
}

method VerboseSimTM(tm_str : string, num_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var i := 0;
  var config := InitConfig;
  while i < num_steps && !config.state.Halt?
    invariant 0 <= i <= num_steps
    decreases num_steps - i
  {
    var cur_symbol := ReadTape(config.tape, config.pos);
    var trans := LookupTrans(tm, config.state.state, cur_symbol);
    print Parse.StateToString(config.state), cur_symbol, "->",
      trans.symbol, Parse.DirToString(trans.dir), Parse.StateToString(trans.state), "\n";
    config := Step(tm, config);
    PrintConfig(config);
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, num_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var config := RunTM(tm, InitConfig, num_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  // VerboseSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000);
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000_000);
}