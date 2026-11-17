module {
  handshake.func @fixed(%arg0: !handshake.channel<f32>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>) attributes {argNames = ["y", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1.000000e+00 : f32} : <>, <f32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %3 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %5 = mux %index [%2, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%3, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 9.99999993E-9 : f32} : <>, <f32>
    %8 = mulf %4, %5 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %9 = subf %4, %8 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %10 = cmpf oge, %9, %7 {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult, %falseResult = cond_br %10, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %10, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_2, %falseResult_3 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %11 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %11, %arg1 : <f32>, <>
  }
}

