module {
  handshake.func @forkBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i16>, !handshake.channel<i8>) attributes {argNames = ["arg0", "start"], resNames = ["out0", "out1"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1:2 = fork [2] %0 {handshake.name = "fork0"} : <i16>
    %2 = trunci %1#1 {handshake.name = "trunci1"} : <i16> to <i8>
    end {handshake.name = "end0"} %1#0, %2 : <i16>, <i8>
  }
}


// -----
module {
  handshake.func @lazyForkBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i16>, !handshake.channel<i8>) attributes {argNames = ["arg0", "start"], resNames = ["out0", "out1"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1:2 = lazy_fork [2] %0 {handshake.name = "lazy_fork0"} : <i16>
    %2 = trunci %1#1 {handshake.name = "trunci1"} : <i16> to <i8>
    end {handshake.name = "end0"} %1#0, %2 : <i16>, <i8>
  }
}


// -----
module {
  handshake.func @mergeBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci1"} : <i32> to <i16>
    %2 = merge %1, %0 {handshake.name = "merge0"} : <i16>
    end {handshake.name = "end0"} %2 : <i16>
  }
}


// -----
module {
  handshake.func @branchBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = br %0 {handshake.name = "br0"} : <i16>
    end {handshake.name = "end0"} %1 : <i16>
  }
}


// -----
module {
  handshake.func @cmergeBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i16>, !handshake.channel<i16>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "out1"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci1"} : <i32> to <i16>
    %result, %index = control_merge [%1, %0]  {handshake.name = "control_merge0"} : [<i16>, <i16>] to <i16>, <i1>
    %2 = extui %index {handshake.name = "extui0"} : <i1> to <i16>
    end {handshake.name = "end0"} %result, %2 : <i16>, <i16>
  }
}


// -----
module {
  handshake.func @muxBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "arg1", "index", "start"], resNames = ["out0"]} {
    %0 = trunci %arg1 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci1"} : <i32> to <i16>
    %2 = trunci %arg2 {handshake.bb = 0 : ui32, handshake.name = "trunci2"} : <i32> to <i1>
    %3 = mux %2 [%1, %0] {handshake.name = "mux0"} : <i1>, [<i16>, <i16>] to <i16>
    end {handshake.name = "end0"} %3 : <i16>
  }
}


// -----
module {
  handshake.func @condBrBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i1>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i16>, !handshake.channel<i8>) attributes {argNames = ["arg0", "cond", "start"], resNames = ["out0", "out1"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %trueResult, %falseResult = cond_br %arg1, %0 {handshake.name = "cond_br0"} : <i1>, <i16>
    %1 = trunci %falseResult {handshake.name = "trunci1"} : <i16> to <i8>
    end {handshake.name = "end0"} %trueResult, %1 : <i16>, <i8>
  }
}


// -----
module {
  handshake.func @bufferBW(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i16> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    %0 = trunci %arg0 {handshake.bb = 0 : ui32, handshake.name = "trunci0"} : <i32> to <i16>
    %1 = buffer %0, bufferType = ONE_SLOT_BREAK_DV, numSlots = 1, dvLatency = 1 {handshake.name = "buffer0"} : <i16>
    end {handshake.name = "end0"} %1 : <i16>
  }
}

