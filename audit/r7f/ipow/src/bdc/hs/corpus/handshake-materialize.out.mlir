module {
  handshake.func @forkArgument(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["toFork", "start"], resNames = ["out0"]} {
    sink %arg1 {handshake.name = "sink0"} : <>
    %0:2 = fork [2] %arg0 {handshake.name = "fork0"} : <i32>
    %1 = addi %0#0, %0#1 {handshake.name = "addi0"} : <i32>
    end {handshake.name = "end0"} %1 : <i32>
  }
  handshake.func @sinkArgument(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["toSink", "start"], resNames = ["out0"]} {
    sink %arg0 {handshake.name = "sink1"} : <i32>
    end {handshake.name = "end1"} %arg1 : <>
  }
  handshake.func @forkResult(%arg0: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = constant %arg0 {handshake.name = "constant0", value = 42 : i32} : <>, <i32>
    %1:2 = fork [2] %0 {handshake.name = "fork1"} : <i32>
    %2 = addi %1#0, %1#1 {handshake.name = "addi1"} : <i32>
    end {handshake.name = "end2"} %2 : <i32>
  }
  handshake.func @sinkResult(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out0"]} {
    %result, %index = control_merge [%arg0]  {handshake.name = "control_merge0"} : [<>] to <>, <i32>
    sink %index {handshake.name = "sink2"} : <i32>
    end {handshake.name = "end3"} %result : <>
  }
  handshake.func @minimizeForkSizes(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    sink %arg1 {handshake.name = "sink3"} : <>
    %0:2 = fork [2] %arg0 {handshake.name = "fork2"} : <i32>
    %1 = addi %0#0, %0#1 {handshake.name = "addi2"} : <i32>
    end {handshake.name = "end4"} %1 : <i32>
  }
  handshake.func @eliminateForkToFork(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    sink %arg1 {handshake.name = "sink4"} : <>
    %0:4 = fork [4] %arg0 {handshake.name = "fork3"} : <i32>
    %1 = addi %0#0, %0#1 {handshake.name = "addi3"} : <i32>
    %2 = addi %0#2, %0#3 {handshake.name = "addi4"} : <i32>
    %3 = addi %1, %2 {handshake.name = "addi5"} : <i32>
    end {handshake.name = "end5"} %3 : <i32>
  }
  handshake.func @eliminateForkToForkMultipleUses(%arg0: !handshake.channel<i32>, %arg1: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "start"], resNames = ["out0"]} {
    sink %arg1 {handshake.name = "sink5"} : <>
    %0:4 = fork [4] %arg0 {handshake.name = "fork4"} : <i32>
    %1 = addi %0#1, %0#0 {handshake.name = "addi6"} : <i32>
    %2 = addi %0#2, %0#3 {handshake.name = "addi7"} : <i32>
    %3 = addi %1, %2 {handshake.name = "addi8"} : <i32>
    end {handshake.name = "end6"} %3 : <i32>
  }
  handshake.func @eraseSingleInputFork(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out0"]} {
    end {handshake.name = "end7"} %arg0 : <>
  }
  handshake.func @doNotEraseSingleInputFork(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out0"]} {
    %0 = lazy_fork [1] %arg0 {handshake.name = "lazy_fork0"} : <>
    %1 = fork [1] %0 {handshake.name = "fork5"} : <>
    end {handshake.name = "end8"} %1 : <>
  }
  handshake.func @makeLSQForkLazyDoNothingArg(%arg0: memref<64xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "addr", "start"], resNames = ["out0", "out1"]} {
    %0:2 = lsq[%arg0 : memref<64xi32>] (%1#1, %1#0, %addressResult, %1#2)  {groupSizes = [1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:3 = fork [3] %arg2 {handshake.name = "fork6"} : <>
    %addressResult, %dataResult = load[%arg1] %0#0 {handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.name = "end9"} %dataResult, %0#1 : <i32>, <>
  }
  handshake.func @makeLSQForkLazyDoNothingFork(%arg0: memref<64xi32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "start"], resNames = ["out0", "out1"]} {
    %0:2 = lsq[%arg0 : memref<64xi32>] (%1#2, %1#0, %addressResult, %1#3)  {groupSizes = [1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:4 = fork [4] %arg1 {handshake.name = "fork7"} : <>
    %2 = constant %1#1 {handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%2] %0#0 {handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.name = "end10"} %dataResult, %0#1 : <i32>, <>
  }
  handshake.func @makeLSQForkLazyNeedLazyAndEager(%arg0: memref<64xi32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "start"], resNames = ["out0", "out1"]} {
    %0:3 = lsq[%arg0 : memref<64xi32>] (%2#1, %1#0, %addressResult, %5#0, %addressResult_0, %5#2)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1:3 = lazy_fork [3] %arg1 {handshake.name = "lazy_fork1"} : <>
    %2:2 = fork [2] %1#2 {handshake.name = "fork8"} : <>
    %3 = constant %2#0 {handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%3] %0#0 {handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %4 = br %1#1 {handshake.name = "br0"} : <>
    %5:3 = fork [3] %4 {handshake.name = "fork9"} : <>
    %6 = constant %5#1 {handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %addressResult_0, %dataResult_1 = load[%6] %0#1 {handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %7 = addi %dataResult, %dataResult_1 {handshake.name = "addi9"} : <i32>
    end {handshake.name = "end11"} %7, %0#2 : <i32>, <>
  }
  handshake.func @makeLSQForkLazyComplex(%arg0: memref<64xi32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["memref", "start"], resNames = ["out0", "out1"]} {
    %0:4 = lsq[%arg0 : memref<64xi32>] (%3#2, %2#0, %addressResult, %6#0, %addressResult_0, %8#0, %addressResult_2, %8#2)  {groupSizes = [1 : i32, 1 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = merge %arg1, %6#1 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <>
    %2:3 = lazy_fork [3] %1 {handshake.bb = 1 : ui32, handshake.name = "lazy_fork2"} : <>
    %3:3 = fork [3] %2#2 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <>
    %4 = constant %3#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %5 = constant %3#1 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%5] %0#0 {handshake.bb = 1 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %trueResult, %falseResult = cond_br %4, %2#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br0"} : <i1>, <>
    sink %dataResult {handshake.name = "sink6"} : <i32>
    %6:3 = lazy_fork [3] %trueResult {handshake.bb = 2 : ui32, handshake.name = "lazy_fork3"} : <>
    %7 = constant %6#2 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %addressResult_0, %dataResult_1 = load[%7] %0#1 {handshake.bb = 2 : ui32, handshake.name = "load5"} : <i32>, <i32>, <i32>, <i32>
    sink %dataResult_1 {handshake.name = "sink7"} : <i32>
    %8:3 = fork [3] %falseResult {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <>
    %9 = constant %8#1 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 2 : i32} : <>, <i32>
    %addressResult_2, %dataResult_3 = load[%9] %0#2 {handshake.bb = 3 : ui32, handshake.name = "load6"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 3 : ui32, handshake.name = "end12"} %dataResult_3, %0#3 : <i32>, <>
  }
  handshake.func @makeLSQForkLazyDoubleLSQ(%arg0: memref<64xi32>, %arg1: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["memref", "start"], resNames = ["out0"]} {
    %0:4 = lazy_fork [4] %arg1 {handshake.name = "lazy_fork4"} : <>
    %1:4 = fork [4] %0#3 {handshake.name = "fork12"} : <>
    %2:2 = lsq[%arg0 : memref<64xi32>] (%1#3, %0#1, %addressResult, %9#1, %addressResult_2, %dataResult_3, %9#2)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq4"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    sink %2#1 {handshake.name = "sink8"} : <>
    %3:2 = lsq[%arg0 : memref<64xi32>] (%1#2, %0#2, %addressResult_0, %9#3, %addressResult_4, %dataResult_5, %9#4)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq5"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    sink %3#1 {handshake.name = "sink9"} : <>
    %4 = constant %1#1 {handshake.bb = 0 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %5:2 = fork [2] %4 {handshake.bb = 0 : ui32, handshake.name = "fork13"} : <i32>
    %6 = constant %1#0 {handshake.bb = 0 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %7:2 = fork [2] %6 {handshake.bb = 0 : ui32, handshake.name = "fork14"} : <i32>
    %addressResult, %dataResult = load[%5#1] %2#0 {handshake.bb = 0 : ui32, handshake.name = "load7"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = load[%7#1] %3#0 {handshake.bb = 0 : ui32, handshake.name = "load8"} : <i32>, <i32>, <i32>, <i32>
    %8 = br %0#0 {handshake.name = "br1"} : <>
    %9:5 = fork [5] %8 {handshake.name = "fork15"} : <>
    %addressResult_2, %dataResult_3 = store[%5#0] %dataResult {handshake.bb = 1 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_4, %dataResult_5 = store[%7#0] %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    end {handshake.bb = 1 : ui32, handshake.name = "end13"} %9#0 : <>
  }
}

