// Does not verify, heap management is sooo hard :(
  
// Efficient code for directly simulating TMs.

include "defs.dfy"
include "parse.dfy"  // Used for testing below.

// Heap allocated version of Tape that stores values in an array
// instead of map for efficiency.
// This tape has fixed size and write outside of that size will fail.
class FixedTape {
  const data : array<Symbol>;  // Ref is const, contents are modified.
  // data[offset] corresponds to pos == 0
  var offset : nat;

  constructor Init(tape_size : nat) {
    this.data := new Symbol[tape_size];
    // Start in middle of tape.
    this.offset := tape_size / 2;
  }

  method Read(pos : int) returns (symb : Symbol) {
    var index : int := pos + offset;
    if 0 <= index < this.data.Length {
      return this.data[index];
    } else {
      return BlankSymbol;
    }
  }

  method Write(pos : int, symb : Symbol) returns (successful : bool)
    modifies this.data
    // TODO: Add more invariants!
  {
    var index := pos + this.offset;
    if 0 <= index < this.data.Length {
      this.data[index] := symb;
      return true;
    } else {
      return false;
    }
  }
}


// Simulate TM using FixedTape
class FixedSimulator {
  const tm : TM;
  const tape : FixedTape;  // Ref is const, tape is mutated.
  var pos : int;
  var state : StateOrHalt;
  var step_num : nat;
  var over_tape : bool;

  constructor Init(tm : TM, tape_size : nat) {
    this.tm := tm;
    this.tape := new FixedTape.Init(tape_size);
    this.pos := 0;
    this.state := RunState(InitState);
    this.step_num := 0;
    this.over_tape := false;
  }

  method Step()
    requires !this.state.Halt? && !this.over_tape
    modifies this, this.tape.data
  {
    var cur_symbol := this.tape.Read(this.pos);
    var trans := LookupTrans(this.tm, this.state.state, cur_symbol);

    var write_succeeded := this.tape.Write(this.pos, trans.symbol);
    if !write_succeeded {
      this.over_tape := true;
    } else {
      this.pos := match(trans.dir) {
        case Right => this.pos + 1
        case Left  => this.pos - 1
      };
      this.state := trans.state;
    }
  }

  method Run(num_steps : nat)
    modifies this, this.tape.data
  {
    var i := 0;
    while i < num_steps && !this.state.Halt? && !this.over_tape {
      this.Step();
      i := i + 1;
    }
  }
}


// Testing
method PrintConfig(sim : FixedSimulator) {
  var cur_symbol := sim.tape.Read(sim.pos);
  print sim.step_num,
        " State: ", StateToString(sim.state),
        " Symbol: ", cur_symbol,
        " Pos: ", sim.pos, "\n";
}

method QuietSimTM(tm_str : string, tape_size : nat, num_steps : nat) {
  var tm := ParseTM(tm_str);
  var sim := new FixedSimulator.Init(tm, tape_size);
  sim.Run(num_steps);
  PrintConfig(sim);
}

method Main() {
  // 4x2 Champion
  QuietSimTM("1RB1LB_1LA0LC_1RZ1LD_1RD0RA", 1000, 1000);
  // 5x2 Champion
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,       1_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,      10_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,     100_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,   1_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000,  10_000_000);
  QuietSimTM("1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 100_000, 100_000_000);
}