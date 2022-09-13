datatype Dir = Right | Left

class Tape<Symbol> {
  var init_symbol : Symbol;  // Const
  var data : map<int, Symbol>;
  var pos : int;

  constructor Init(in_init_symbol : Symbol) {
    init_symbol := in_init_symbol;
    data := map[];
    pos := 0;
  }

  method Read() returns (symb : Symbol) {
    if pos in data {
      return data[pos];
    } else {
      return init_symbol;
    }
  }

  method Write(symb : Symbol)
    modifies this
  {
    data := data[pos := symb];
  }

  method Move(dir : Dir)
    modifies this
  {
    if dir == Right {
      pos := pos + 1;
    } else {
      pos := pos - 1;
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
    if key in data {
      return data[key];
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
  var tape : Tape<Symbol>;
  var cur_state : State;

  var halted : bool;
  var step_num : nat;

  constructor Init(in_tm : TM<State, Symbol>) {
    tm := in_tm;
    tape := new Tape.Init(in_tm.init_symbol);
    cur_state := in_tm.init_state;
    halted := false;
    step_num := 0;
  }

  method Step()
    modifies this, tape
  {
    if !halted {
      var cur_symbol := tape.Read();
      var trans := tm.trans_table.Lookup(
        state := cur_state, symbol := cur_symbol);
      match(trans) {
        case Halt => halted := true;
        case Transition(symbol2write, new_state, dir) => {
          tape.Write(trans.symbol);
          cur_state := new_state;
          tape.Move(dir);
        }
      }

    }
  }

  // method Seek(target_step_num : int)
  //   modifies this, tape
  // {
  //   while !halted && step_num < target_step_num {
  //     Step();
  //   }
  // }
}