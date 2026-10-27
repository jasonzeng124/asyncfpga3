module {
  handshake.func @mergeBufferTwoInputs(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0:2 = fork [2] %arg0 {handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "fork0"} : <>
    %1 = merge %0#0, %0#1 {handshake.name = "merge0"} : <>
    end {handshake.name = "end0"} %1 : <>
  }
}


// -----
module {
  handshake.func @mcUnbuffered(%arg0: memref<64xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "addr", "start"], resNames = ["out0", "out1"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<64xi32>] %0#0 (%addressResult) %0#1 {connectedBlocks = [0 : i32], handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "2": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = fork [2] %arg2 {handshake.bb = 0 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "fork0"} : <>
    %addressResult, %dataResult = load[%arg1] %outputs {handshake.bb = 0 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "1": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.name = "end0"} %dataResult, %memEnd : <i32>, <>
  }
}


// -----
module {
  handshake.func @lsqUnbuffered(%arg0: memref<64xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "addr", "start"], resNames = ["out0", "out1"]} {
    %0:2 = lsq[%arg0 : memref<64xi32>] (%1#0, %1#1, %addressResult, %1#2)  {groupSizes = [1 : i32], handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "2": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "3": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "fork0"} : <>
    %addressResult, %dataResult = load[%arg1] %0#0 {handshake.bb = 0 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "1": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.name = "end0"} %dataResult, %0#1 : <i32>, <>
  }
}


// -----
module {
  handshake.func @lsqBufferControlPath(%arg0: memref<64xi32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "start"], resNames = ["out0", "out1"]} {
    %0:4 = lsq[%arg0 : memref<64xi32>] (%2#4, %2#0, %addressResult, %5#0, %addressResult_0, %7#0, %addressResult_2, %7#2)  {groupSizes = [1 : i32, 1 : i32, 1 : i32], handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "2": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "3": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "4": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "5": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "6": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "7": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = merge %arg1, %5#2 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00, "1": [0,inf], [1,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "merge0"} : <>
    %2:5 = lazy_fork [5] %1 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"0": [0,inf], [0,inf], 1, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "lazy_fork0"} : <>
    %3 = constant %2#1 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"0": [1,inf], [0,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "constant0", value = false} : <>, <i1>
    %4 = constant %2#2 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"0": [1,inf], [0,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%4] %0#0 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"1": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %trueResult, %falseResult = cond_br %3, %2#3 {handshake.bb = 1 : ui32, handshake.bufProps = #handshake<bufProps{"1": [0,inf], [1,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "cond_br0"} : <i1>, <>
    sink %dataResult {handshake.name = "sink0"} : <i32>
    %5:3 = lazy_fork [3] %trueResult {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %6 = constant %5#1 {handshake.bb = 2 : ui32, handshake.bufProps = #handshake<bufProps{"0": [1,inf], [0,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %addressResult_0, %dataResult_1 = load[%6] %0#1 {handshake.bb = 2 : ui32, handshake.bufProps = #handshake<bufProps{"1": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    sink %dataResult_1 {handshake.name = "sink1"} : <i32>
    %7:3 = lazy_fork [3] %falseResult {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %8 = constant %7#1 {handshake.bb = 3 : ui32, handshake.bufProps = #handshake<bufProps{"0": [1,inf], [0,inf], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %addressResult_2, %dataResult_3 = load[%8] %0#2 {handshake.bb = 3 : ui32, handshake.bufProps = #handshake<bufProps{"1": [0,0], [0,0], 0, 0.000000e+00, 0.000000e+00, 0.000000e+00}>, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %dataResult_3, %0#3 : <i32>, <>
  }
}

