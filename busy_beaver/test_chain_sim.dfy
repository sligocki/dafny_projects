include "chain_sim.dfy"

// Tests
import opened ChainSimNat

method VerboseSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var i := 0;
  var config := InitConfig(tm);
  while i < num_sim_steps && config.Config? && !TMSpec.IsHalt?(config.state)
    invariant 0 <= i <= num_sim_steps
    decreases num_sim_steps - i
  {
    config := Step(tm, config);
    PrintConfig(config);
    if config.Config? {
      print "Tape:  Left: ";
      if TMSpec.Left in config.tape.data {
        PrintSemiTape(config.tape.data[TMSpec.Left]);
      }
      print "  /  Right: ";
      if TMSpec.Right in config.tape.data {
        PrintSemiTape(config.tape.data[TMSpec.Right]);
      }
      print "\n";
    }
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, num_sim_steps : nat) {
  var tm := Parse.ParseTM(tm_str);
  var config := RunTM(tm, InitConfig(tm), num_sim_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  // VerboseSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 108);
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000_000);
}
