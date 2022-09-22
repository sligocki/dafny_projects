datatype Dir = Right | Left

class Tape<Symbol> {
  const init_symbol : Symbol;
  var data : map<int, Symbol>;
  var pos : int;

  constructor Init(in_init_symbol : Symbol) {
    this.init_symbol := in_init_symbol;
    this.data := map[];
    this.pos := 0;
  }

  method Read() returns (symb : Symbol) {
    if this.pos in this.data {
      return this.data[this.pos];
    } else {
      return this.init_symbol;
    }
  }

  method Write(symb : Symbol)
    modifies this
  {
    this.data := this.data[this.pos := symb];
  }

  method Move(dir : Dir)
    modifies this
  {
    match(dir) {
      case Right => this.pos := this.pos + 1;
      case Left  => this.pos := this.pos - 1;
    }
  }
}


datatype TransKey<State, Symbol> = TransKey(
  state : State,
  symbol : Symbol
)

datatype Transition<State(==), Symbol(==)> =
  Halt |
  Transition(symbol : Symbol, state : State, dir : Dir)

class TransTable<State(==), Symbol(==)> {
  var data : map<TransKey<State, Symbol>, Transition<State, Symbol>>;

  method Lookup(state : State, symbol : Symbol)
    returns (trans : Transition<State, Symbol>) {
    var key := TransKey(state := state, symbol := symbol);
    if key in this.data {
      return this.data[key];
    } else {
      return Halt;
    }
  }
} 

datatype TM<State(==), Symbol(==)> = TM(
  init_state : State,
  init_symbol : Symbol,
  trans_table : TransTable<State, Symbol>
)


class Simulator<State(==), Symbol(==)> {
  var tm : TM<State, Symbol>;
  // Note: const here means that the reference will never change.
  // (The tape itself will be modified).
  const tape : Tape<Symbol>;
  var cur_state : State;

  var halted : bool;
  var step_num : nat;

  constructor Init(in_tm : TM<State, Symbol>) {
    this.tm := in_tm;
    this.tape := new Tape.Init(in_tm.init_symbol);
    this.cur_state := in_tm.init_state;
    this.halted := false;
    this.step_num := 0;
  }

  method Step()
    modifies this, this.tape
    ensures halted || step_num > old(step_num)
  {
    if !this.halted {
      var cur_symbol := this.tape.Read();
      var trans := this.tm.trans_table.Lookup(
        state := this.cur_state, symbol := cur_symbol);
      match(trans) {
        case Halt => this.halted := true;
        case Transition(symbol2write, new_state, dir) => {
          this.tape.Write(symbol2write);
          this.cur_state := new_state;
          this.tape.Move(dir);
        }
      }
      this.step_num := this.step_num + 1;
    }
  }

  method Seek(target_step_num : int)
    modifies this, this.tape
    ensures this.tape == old(this.tape)
  {
    while !this.halted && this.step_num < target_step_num {
      this.Step();
    }
  }
}

