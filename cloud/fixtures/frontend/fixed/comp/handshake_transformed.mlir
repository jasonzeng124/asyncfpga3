module {
  handshake.func @fixed(%arg0: !handshake.channel<f32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>) attributes {argNames = ["y", "start"], resNames = ["out0", "end"]} {
    %0:3 = fork [3] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1 = constant %0#2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1.000000e+00 : f32} : <>, <f32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %4 = br %0#1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %9#0 [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %6:2 = fork [2] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <f32>
    %7 = mux %9#1 [%3, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <f32>
    %result, %index = control_merge [%4, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 9.99999993E-9 : f32} : <>, <f32>
    %12 = mulf %6#1, %8#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <f32>
    %14 = subf %6#0, %13#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %15 = cmpf oge, %14, %11 {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %16:3 = fork [3] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %16#2, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %16#1, %8#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    sink %falseResult_1 {handshake.name = "sink0"} : <f32>
    %trueResult_2, %falseResult_3 = cond_br %16#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    sink %falseResult_3 {handshake.name = "sink1"} : <>
    %17 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %17, %0#0 : <f32>, <>
  }
}

