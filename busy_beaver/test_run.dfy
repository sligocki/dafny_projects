include "defs.dfy"
include "impl.dfy"
include "parse.dfy"

method RunTM(tm_str : string, num_steps : nat) {
  var tm := ParseTM(tm_str);
  var config := RunTM(tm, InitConfig, num_steps);
  if config.state.Halt? {
    print "TM Halted\n";
  } else {
    print "TM State: ", config.state.state, "\n";
  }
}