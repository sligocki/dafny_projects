// Define macro machines as abstractions over a base Turing Machine.

include "tm_spec_gen.dfy"
include "chain_sim.dfy"
include "parse.dfy"  // Used for testing below.

abstract module BlockMacroSpecAbstract refines TMSpecGenAbstract {
  import BaseSpec : TMSpecGenAbstract

  type Symbol = seq<BaseSpec.Symbol>
  type State = BaseSpec.State
  datatype TM = BlockMacro(base_tm : BaseSpec.TM, block_size : nat)

  function method IsHalt?(state : State) : bool { BaseSpec.IsHalt?(state) }
  function method BlankSymbol(tm : TM) : Symbol {
    seq(tm.block_size, n => BaseSpec.BlankSymbol(tm.base_tm))
  }
  function method InitState(tm : TM) : State { BaseSpec.InitState(tm.base_tm) }
  function method HaltState(tm : TM) : State { BaseSpec.HaltState(tm.base_tm) }

  function method ScoreSymbol(symbol : Symbol) : nat {
    1 // TODO
  }
  function method ScoreState(state : State) : nat { 0 }
  

  datatype BoundedSimResult =
    | InfiniteInBlock
    | HaltedInBlock(
      new_block : seq<BaseSpec.Symbol>,
      new_pos : nat,
      num_base_steps : nat
    )
    | ExittedBlock(
      new_block : seq<BaseSpec.Symbol>,
      new_state : BaseSpec.State,
      new_dir : Dir,
      num_base_steps : nat
    )

  method BoundedSim(base_tm : BaseSpec.TM, state : BaseSpec.State,
                    start_tape : seq<BaseSpec.Symbol>, pos : int, dir : Dir)
    returns (result : BoundedSimResult)
  {
    var num_base_steps : nat := 0;
    print "ERROR: BoundedSim Not Implemented!\n";
  }

  method LookupTrans(tm : TM, state : State, symbol : Symbol, dir : Dir)
    returns (trans : Transition)
  {
    var block : seq<BaseSpec.Symbol> := symbol;
    var pos_in_block := match dir
      case Right => 0
      case Left => |block| - 1;
    var sim_result := BoundedSim(
      tm.base_tm, state, block, pos_in_block, dir);
    match sim_result {
      case InfiniteInBlock =>
        return InfiniteTrans;
      case HaltedInBlock(_, _, _) =>
        // This is not 100% accurate, but good enough for scoring / step count.
        // TODO: Keep track of exact halt location inside new_block.
        return Transition(sim_result.new_block, Right, HaltState(tm),
                          sim_result.num_base_steps);
      case ExittedBlock(_, _, _, _) =>
        return Transition(sim_result.new_block, sim_result.new_dir,
                          sim_result.new_state,
                          sim_result.num_base_steps);
    }
  }
}

module BlockMacroSpecNat refines BlockMacroSpecAbstract {
  import BaseSpec = TMSpecGenNat
}

module ChainSimBlock refines ChainSimAbstract {
  import opened TMSpec = BlockMacroSpecNat
}


// Test
import opened ChainSimBlock

method VerboseSimTM(tm_str : string, block_size : nat, num_sim_steps : nat)
  requires block_size > 0
{
  var base_tm := Parse.ParseTM(tm_str);
  var tm := BlockMacroSpecNat.BlockMacro(base_tm, block_size);
  var i := 0;
  var config := InitConfig(tm);
  while i < num_sim_steps && config.Config? && config.state.RunState?
    invariant 0 <= i <= num_sim_steps
    decreases num_sim_steps - i
  {
    config := Step(tm, config);
    PrintConfig(config);
    if config.Config? {
      print "Tape:  Left: ";
      if BlockMacroSpecNat.Left in config.tape.data {
        PrintSemiTape(config.tape.data[BlockMacroSpecNat.Left]);
      }
      print "  /  Right: ";
      if BlockMacroSpecNat.Right in config.tape.data {
        PrintSemiTape(config.tape.data[BlockMacroSpecNat.Right]);
      }
      print "\n";
    }
    i := i + 1;
  }
}

method QuietSimTM(tm_str : string, block_size : nat, num_sim_steps : nat)
  requires block_size > 0
{
  var base_tm := Parse.ParseTM(tm_str);
  var tm := BlockMacroSpecNat.BlockMacro(base_tm, block_size);
  var config := RunTM(tm, InitConfig(tm), num_sim_steps);
  PrintConfig(config);
}

method Main() {
  // 4x2 Champion
  // VerboseSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 2, 108);
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 2, 1000);
  // 5x2 Champion (Block size 3)
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3,  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 3, 100_000_000);
}
