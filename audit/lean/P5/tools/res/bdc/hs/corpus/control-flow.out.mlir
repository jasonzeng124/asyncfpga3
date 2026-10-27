module {
  handshake.func @selfLoop(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["in0", "in1", "start"], resNames = ["end"]} {
    %0 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br0"} : <i32>
    %1 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = mux %index [%0, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%1, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = cmpi eq, %3, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %5, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %5, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %5, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %arg2 : <>
  }
}


// -----
module {
  handshake.func @duplicateLiveOut(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["in0", "in1", "in2", "start"], resNames = ["end"]} {
    %trueResult, %falseResult = cond_br %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %arg0, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %0 = mux %index [%trueResult, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %1 = mux %index [%falseResult_1, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %2 = mux %index [%trueResult, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_3, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 1 : ui32, handshake.name = "end0"} %arg3 : <>
  }
}


// -----
module {
  handshake.func @divergeSameArg(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> !handshake.control<> attributes {argNames = ["in0", "in1", "start"], resNames = ["end"]} {
    %trueResult, %falseResult = cond_br %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br0"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %arg0, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br1"} : <i1>, <>
    %0 = merge %trueResult {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %result, %index = control_merge [%trueResult_0]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %1 = br %result {handshake.bb = 1 : ui32, handshake.name = "br0"} : <>
    %2 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_2, %index_3 = control_merge [%falseResult_1]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %3 = br %result_2 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <>
    %result_4, %index_5 = control_merge [%1, %3]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %arg2 : <>
  }
}

