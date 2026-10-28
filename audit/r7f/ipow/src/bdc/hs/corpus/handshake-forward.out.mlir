module {
  handshake.func @forkFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i32>) attributes {argNames = ["arg0", "start"], resNames = ["out0", "out1"]} {
    %0:2 = fork [2] %arg0 {handshake.name = "fork0"} : <i16>
    %1 = extsi %0#1 {handshake.name = "extsi0"} : <i16> to <i32>
    %2 = extsi %0#0 {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2, %1 : <i32>, <i32>
  }
}


// -----
module {
  handshake.func @lazyForkFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i32>) attributes {argNames = ["arg0", "start"], resNames = ["out0", "out1"]} {
    %0:2 = lazy_fork [2] %arg0 {handshake.name = "lazy_fork0"} : <i16>
    %1 = extsi %0#1 {handshake.name = "extsi0"} : <i16> to <i32>
    %2 = extsi %0#0 {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2, %1 : <i32>, <i32>
  }
}


// -----
module {
  handshake.func @mergeFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %1 = merge %0, %arg1 {handshake.name = "merge0"} : <i16>
    %2 = extsi %1 {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @branchFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = br %arg0 {handshake.name = "br0"} : <i16>
    %1 = extsi %0 {handshake.name = "extsi0"} : <i16> to <i32>
    end {handshake.name = "end0"} %1 : <i32>
  }
}


// -----
module {
  handshake.func @cmergeFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i8>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "out1"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %result, %index = control_merge [%0, %arg1]  {handshake.name = "control_merge0"} : [<i16>, <i16>] to <i16>, <i1>
    %1 = extsi %result {handshake.name = "extsi1"} : <i16> to <i32>
    %2 = extui %index {handshake.name = "extui0"} : <i1> to <i8>
    end {handshake.name = "end0"} %1, %2 : <i32>, <i8>
  }
}


// -----
module {
  handshake.func @muxFW(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i8>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "index", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i16>
    %1 = trunci %arg2 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i8> to <i1>
    %2 = mux %1 [%0, %arg1] {handshake.name = "mux0"} : <i1>, [<i16>, <i16>] to <i16>
    %3 = extsi %2 {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @mux_si_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i8>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "index", "start"], resNames = ["out0"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i17>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i17>
    %2 = trunci %arg2 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i8> to <i1>
    %3 = mux %2 [%1, %0] {handshake.name = "mux0"} : <i1>, [<i17>, <i17>] to <i17>
    %4 = extsi %3 {handshake.name = "extsi1"} : <i17> to <i32>
    end {handshake.name = "end0"} %4 : <i32>
  }
}


// -----
module {
  handshake.func @mux_ui_si(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i8>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "index", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i16>
    %1 = trunci %arg2 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i8> to <i1>
    %2 = mux %1 [%0, %arg1] {handshake.name = "mux0"} : <i1>, [<i16>, <i16>] to <i16>
    %3 = extsi %2 {handshake.name = "extsi0"} : <i16> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @mux_ui_ui(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i8>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "index", "start"], resNames = ["out0"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i8> to <i16>
    %1 = trunci %arg2 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i8> to <i1>
    %2 = mux %1 [%0, %arg1] {handshake.name = "mux0"} : <i1>, [<i16>, <i16>] to <i16>
    %3 = extui %2 {handshake.name = "extui1"} : <i16> to <i32>
    end {handshake.name = "end0"} %3 : <i32>
  }
}


// -----
module {
  handshake.func @condBrFw(%arg0: !handshake.channel<i16>, %arg1: !handshake.channel<i1>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i32>) attributes {argNames = ["arg0", "cond", "start"], resNames = ["out0", "out1"]} {
    %trueResult, %falseResult = cond_br %arg1, %arg0 {handshake.name = "cond_br0"} : <i1>, <i16>
    %0 = extsi %falseResult {handshake.name = "extsi0"} : <i16> to <i32>
    %1 = extsi %trueResult {handshake.name = "extsi1"} : <i16> to <i32>
    end {handshake.name = "end0"} %1, %0 : <i32>, <i32>
  }
}


// -----
module {
  handshake.func @bufferFW(%arg0: !handshake.channel<i16>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = buffer %arg0, bufferType = ONE_SLOT_BREAK_DV, numSlots = 1, dvLatency = 1 {handshake.name = "buffer0"} : <i16>
    %1 = extsi %0 {handshake.name = "extsi0"} : <i16> to <i32>
    end {handshake.name = "end0"} %1 : <i32>
  }
}

