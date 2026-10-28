module {
  handshake.func @eraseUnconditionalBranches(%arg0: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["start"], resNames = ["out0"]} {
    end {handshake.name = "end0"} %arg0 : <>
  }
  handshake.func @eraseSingleInputMerges(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = merge %arg0, %arg1 {handshake.name = "merge0"} : <i32>
    %1 = addi %arg0, %0 {handshake.name = "addi0"} : <i32>
    end {handshake.name = "end1"} %1 : <i32>
  }
  handshake.func @eraseSingleInputMuxes(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i1>, %arg3: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "cond", "start"], resNames = ["out0"]} {
    sink %arg2 {handshake.name = "sink0"} : <i1>
    %0 = mux %arg2 [%arg0, %arg1] {handshake.bb = 0 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %1 = addi %arg0, %0 {handshake.name = "addi1"} : <i32>
    end {handshake.name = "end2"} %1 : <i32>
  }
  handshake.func @eraseSingleControlMerges(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %result, %index = control_merge [%arg0, %arg1]  {handshake.bb = 0 : ui32, handshake.name = "control_merge0"} : [<i32>, <i32>] to <i32>, <i32>
    %2 = addi %arg0, %arg1 {handshake.name = "addi2"} : <i32>
    %3 = addi %2, %result {handshake.name = "addi3"} : <i32>
    %4 = addi %1, %index {handshake.name = "addi4"} : <i32>
    %5 = addi %3, %4 {handshake.name = "addi5"} : <i32>
    end {handshake.name = "end3"} %5 : <i32>
  }
  handshake.func @downgradeIndexlessControlMerge(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.channel<i32> attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0"]} {
    %0 = merge %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "merge1"} : <i32>
    end {handshake.name = "end4"} %0 : <i32>
  }
}

