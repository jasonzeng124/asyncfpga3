module {
  handshake.func @addiBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %2 = addi %1, %0 {handshake.name = "addi0"} : <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @subiBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %2 = subi %1, %0 {handshake.name = "subi0"} : <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @muliBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.name = "extsi0"} : <i8> to <i32>
    %1 = muli %0, %arg1 {handshake.name = "muli0"} : <i32>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i32> to <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @andiBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i8>
    %1 = andi %arg0, %0 {handshake.name = "andi0"} : <i8>
    %2 = extui %1 {handshake.name = "extui0"} : <i8> to <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @oriBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.name = "extui0"} : <i8> to <i32>
    %1 = ori %0, %arg1 {handshake.name = "ori0"} : <i32>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i32> to <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @xoriBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.name = "extui0"} : <i8> to <i32>
    %1 = xori %0, %arg1 {handshake.name = "xori0"} : <i32>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i32> to <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @shliBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = constant %arg1 {handshake.name = "constant0", value = 4 : i32} : <>, <i32>
    %1 = shli %arg0, %0 {handshake.name = "shli0"} : <i32>
    %2 = trunci %1 {handshake.name = "trunci0"} : <i32> to <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @shrsiBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i20>
    %1 = constant %arg1 {handshake.name = "constant0", value = 4 : i20} : <>, <i20>
    %2 = shrsi %0, %1 {handshake.name = "shrsi0"} : <i20>
    %3 = trunci %2 {handshake.name = "trunci1"} : <i20> to <i16>
    end {handshake.name = "end0"} %3 : <i16>
  }
}


// -----
module {
  handshake.func @shruiBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i20>
    %1 = constant %arg1 {handshake.name = "constant0", value = 4 : i20} : <>, <i20>
    %2 = shrui %0, %1 {handshake.name = "shrui0"} : <i20>
    %3 = trunci %2 {handshake.name = "trunci1"} : <i20> to <i16>
    end {handshake.name = "end0"} %3 : <i16>
  }
}


// -----
module {
  handshake.func @selectBW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i1>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "select", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %2 = select %arg2[%1, %0] {handshake.name = "select0"} : <i1>, <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}

