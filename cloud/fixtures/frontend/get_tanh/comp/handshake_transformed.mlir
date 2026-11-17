module {
  handshake.func @get_tanh(%arg0: memref<1000xf32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "addr", "A_start", "addr_start", "start"], resNames = ["A_end", "addr_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult) %50#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1:2 = lsq[%arg0 : memref<1000xf32>] (%arg2, %8#0, %addressResult_0, %41#0, %addressResult_14, %dataResult_15, %50#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i1> to <i10>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %7:2 = fork [2] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %result, %index = control_merge [%5, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %9 = constant %8#2 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1.000000e+00 : f32} : <>, <f32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <f32>
    %addressResult, %dataResult = load[%7#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %11:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %12 = trunci %11#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %13 = trunci %11#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %addressResult_0, %dataResult_1 = load[%13] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %14:2 = fork [2] %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <f32>
    %15 = cmpf ult, %14#0, %10#1 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %16:5 = fork [5] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %16#1, %7#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i10>
    %trueResult_2, %falseResult_3 = cond_br %16#0, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i10>
    %trueResult_4, %falseResult_5 = cond_br %16#4, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    sink %falseResult_5 {handshake.name = "sink0"} : <f32>
    %trueResult_6, %falseResult_7 = cond_br %16#3, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %16#2, %10#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    sink %trueResult_8 {handshake.name = "sink1"} : <f32>
    %17 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i10>
    %18 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i10>
    %19 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %20:5 = fork [5] %19 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <f32>
    %result_10, %index_11 = control_merge [%trueResult_6]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink2"} : <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 3.70476198 : f32} : <>, <f32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 19.5238094 : f32} : <>, <f32>
    %25 = mulf %20#3, %20#4 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %26 = addf %25, %24 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %27 = mulf %26, %20#2 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %28 = mulf %27, %20#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf2"} : <f32>
    %29 = addf %28, %22 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %30 = mulf %29, %20#0 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf3"} : <f32>
    %31 = br %30 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <f32>
    %32 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i10>
    %33 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i10>
    %34 = br %result_10 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %35 = mux %40#2 [%falseResult_9, %31] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %36 = mux %40#1 [%falseResult, %32] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i10>, <i10>] to <i10>
    %37 = extui %36 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i10> to <i11>
    %38 = constant %43 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i11} : <>, <i11>
    %39 = mux %40#0 [%falseResult_3, %33] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %result_12, %index_13 = control_merge [%falseResult_7, %34]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %40:3 = fork [3] %index_13 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i1>
    %41:2 = lazy_fork [2] %result_12 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork1"} : <>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %43 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %addressResult_14, %dataResult_15 = store[%39] %35 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store2"} : <i10>, <f32>, <i10>, <f32>
    %44 = addi %37, %38 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i11>
    %45:2 = fork [2] %44 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i11>
    %46 = trunci %45#0 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i11> to <i10>
    %47 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1000 : i11} : <>, <i11>
    %48 = cmpi ult, %45#1, %47 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i11>
    %49:2 = fork [2] %48 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %49#0, %46 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i10>
    sink %falseResult_17 {handshake.name = "sink3"} : <i10>
    %trueResult_18, %falseResult_19 = cond_br %49#1, %41#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_21 {handshake.name = "sink4"} : <i1>
    %50:2 = fork [2] %result_20 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

