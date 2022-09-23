include "tape.dfy"
include "turing_machine.dfy"

abstract module Simulator {
  import Tape : TapeInterface
  import TM = Tape.TM

  datatype Config = Config(
    tape : Tape.Tape,
    pos : int,
    state : TM.StateOrHalt,
    step_num : nat
  )

  function InitConfig(tm : TM.TM) : Config {
    Config(
      tape := Tape.Blank(TM.InitSymbol(tm)),
      pos := 0,
      state := TM.RunState(TM.InitState(tm)),
      step_num := 0
    )
  }

  function Step(tm : TM.TM, config : Config) : Config
    requires config.state != TM.Halt
  {
    var cur_symbol := Tape.Read(config.tape, config.pos);
    var trans := TM.LookupTrans(tm, config.state.state, cur_symbol);
    Config(
      tape := Tape.Write(config.tape, config.pos, trans.symbol),
      pos := match(trans.dir) {
        case Right => config.pos + 1
        case Left  => config.pos - 1
      },
      state := trans.state,
      step_num := config.step_num + 1
    )
  }

  function Seek(tm : TM.TM, config : Config, target_step_num : nat) : Config {
    if (config.state.Halt? || config.step_num >= target_step_num)
    then
      config
    else
      Step(tm, config)
  }

  predicate tm_halts(tm: TM.TM) {
    exists n : nat :: Seek(tm, InitConfig(tm), n).state.Halt?
  }
}