include "defs.dfy"

// Implementation of efficient methods mirroring specification in defs.dfy

lemma StepNHalt(tm : TM, start_config : Config, n : nat, m : nat)
  requires StepN(tm, start_config, n).state.Halt?
  requires m >= n
  ensures StepN(tm, start_config, m) == StepN(tm, start_config, n)

method RunTM(tm : TM, start_config : Config, num_steps : nat) returns (end_config : Config)
  ensures end_config == StepN(tm, start_config, num_steps)
{
  var i := 0;
  var cur_config := start_config;
  while i < num_steps && !cur_config.state.Halt?
    invariant 0 <= i <= num_steps
    invariant cur_config == StepN(tm, start_config, i)
  {
    cur_config := Step(tm, cur_config);
    i := i + 1;
  }
  if cur_config.state.Halt? {
    StepNHalt(tm, start_config, i, num_steps);
  }
  assert cur_config == StepN(tm, start_config, num_steps);
  return cur_config;
}