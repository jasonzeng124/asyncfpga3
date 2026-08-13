module {
  handshake.func @cmergeToMuxIndexOpt(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.channel<i32>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "out1"]} {
    %result, %index = control_merge [%arg0, %arg1]  {handshake.name = "control_merge0"} : [<i32>, <i32>] to <i32>, <i1>
    %0 = mux %index [%arg0, %arg1] {handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    end {handshake.name = "end0"} %result, %0 : <i32>, <i32>
  }
}


// -----
module {
  handshake.func @cmergeToMuxIndexOpt(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %result, %index = control_merge [%arg0]  {handshake.name = "control_merge0"} : [<i32>] to <i32>, <i1>
    %result_0, %index_1 = control_merge [%arg1]  {handshake.name = "control_merge1"} : [<i32>] to <i32>, <i1>
    %0 = extui %index_1 {handshake.name = "extui0"} : <i1> to <i32>
    %1 = addi %result_0, %0 {handshake.name = "addi0"} : <i32>
    %2 = addi %1, %result {handshake.name = "addi1"} : <i32>
    end {handshake.name = "end0"} %2 : <i32>
  }
}


// -----
module {
  handshake.func @memAddrOpt(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["mem", "mem_start", "start"], resNames = ["out0", "out1"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg1 (%3, %addressResult, %addressResult_0, %dataResult_1, %addressResult_2, %dataResult_3) %arg2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg2 {handshake.name = "constant0", value = 0 : i10} : <>, <i10>
    %1 = constant %arg2 {handshake.name = "constant1", value = 500 : i10} : <>, <i10>
    %2 = constant %arg2 {handshake.name = "constant2", value = 42 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%0] %outputs {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_0, %dataResult_1 = store[%1] %2 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i10>, <i32>, <i10>, <i32>
    %4 = constant %arg2 {handshake.name = "constant4", value = -25 : i10} : <>, <i10>
    %addressResult_2, %dataResult_3 = store[%4] %2 {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    end {handshake.name = "end0"} %dataResult, %memEnd : <i32>, <>
  }
}


// -----
module {
  handshake.func @memAddrOptMasterSlave(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["mem", "mem_start", "start"], resNames = ["out0", "out1"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg1 (%4, %addressResult_2, %dataResult_3, %0#1, %0#2, %0#3) %arg2 {connectedBlocks = [0 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0:4 = lsq[MC] (%arg2, %addressResult, %addressResult_0, %dataResult_1, %outputs)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>)
    %1 = constant %arg2 {handshake.name = "constant0", value = 0 : i10} : <>, <i10>
    %2 = constant %arg2 {handshake.name = "constant1", value = 500 : i10} : <>, <i10>
    %3 = constant %arg2 {handshake.name = "constant2", value = 42 : i32} : <>, <i32>
    %4 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%1] %0#0 {handshake.bb = 0 : ui32, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_0, %dataResult_1 = store[%2] %3 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i10>, <i32>, <i10>, <i32>
    %5 = constant %arg2 {handshake.name = "constant4", value = -25 : i10} : <>, <i10>
    %addressResult_2, %dataResult_3 = store[%5] %3 {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    end {handshake.name = "end0"} %dataResult, %memEnd : <i32>, <>
  }
}


// -----
module {
  handshake.func @simpleCycle(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i1>, %arg2: !handshake.channel<i1>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "index", "cond", "start"], resNames = ["out0"]} {
    %0 = mux %arg1 [%arg0, %trueResult] {handshake.name = "mux0"} : <i1>, [<i8>, <i8>] to <i8>
    %trueResult, %falseResult = cond_br %arg2, %0 {handshake.name = "cond_br0"} : <i1>, <i8>
    %1 = extsi %falseResult {handshake.name = "extsi0"} : <i8> to <i32>
    end {handshake.name = "end0"} %1 : <i32>
  }
}


// -----
module {
  handshake.func @complexCycle(%arg0: !handshake.channel<i8>, %arg1: !handshake.channel<i16>, %arg2: !handshake.channel<i24>, %arg3: !handshake.channel<i2>, %arg4: !handshake.channel<i1>, %arg5: !handshake.channel<i1>, %arg6: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "arg2", "bigIndex", "index", "cond", "start"], resNames = ["out0"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i8> to <i24>
    %1 = extsi %arg1 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i16> to <i24>
    %2 = mux %arg3 [%0, %trueResult, %trueResult_0, %trueResult_2] {handshake.name = "mux2"} : <i2>, [<i24>, <i24>, <i24>, <i24>] to <i24>
    %trueResult, %falseResult = cond_br %arg5, %2 {handshake.name = "cond_br2"} : <i1>, <i24>
    %3 = mux %arg4 [%1, %falseResult] {handshake.name = "mux1"} : <i1>, [<i24>, <i24>] to <i24>
    %trueResult_0, %falseResult_1 = cond_br %arg5, %3 {handshake.name = "cond_br1"} : <i1>, <i24>
    %4 = mux %arg4 [%arg2, %falseResult_1] {handshake.name = "mux0"} : <i1>, [<i24>, <i24>] to <i24>
    %trueResult_2, %falseResult_3 = cond_br %arg5, %4 {handshake.name = "cond_br0"} : <i1>, <i24>
    %5 = extsi %falseResult_3 {handshake.name = "extsi2"} : <i24> to <i32>
    end {handshake.name = "end0"} %5 : <i32>
  }
}

