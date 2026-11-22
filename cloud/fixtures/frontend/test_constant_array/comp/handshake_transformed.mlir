module {
  handshake.func @test_constant_array(%arg0: memref<9xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["di", "di_start", "start"], resNames = ["out0", "di_end", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<9xi32>] %arg1 (%addressResult) %72#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%1 : memref<9xi32>] %0#1 (%addressResult_4) %72#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    sink %memEnd_1 {handshake.name = "sink0"} : <>
    %1 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9]> : tensor<9xi32>} : () -> memref<9xi32>
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %5 = extui %4#1 {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %6 = extui %4#0 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %7 = br %0#3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %8 = mux %11#1 [%5, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %11#0 [%6, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i2>, <i2>] to <i2>
    %10:3 = fork [3] %9 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i2>
    %result, %index = control_merge [%7, %trueResult_22]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %12:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %13 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %14 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %15 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i1> to <i2>
    %16 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %17 = br %10#2 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i2>
    %18 = br %10#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i2>
    %19 = br %10#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i2>
    %20 = br %12#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %21 = mux %37#3 [%15, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %22:3 = fork [3] %21 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i2>
    %23 = extui %22#0 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i2> to <i4>
    %24 = extui %22#1 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i2> to <i4>
    %25 = extui %22#2 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i2> to <i3>
    %26 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i3} : <>, <i3>
    %27 = mux %37#4 [%16, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %28 = mux %37#2 [%17, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i2>, <i2>] to <i2>
    %29 = mux %37#0 [%18, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i2>, <i2>] to <i2>
    %30:3 = fork [3] %29 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i2>
    %31 = extui %30#0 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i2> to <i4>
    %32 = extui %30#2 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i2> to <i64>
    %33 = mux %37#1 [%19, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i2>, <i2>] to <i2>
    %34:3 = fork [3] %33 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i2>
    %35 = extui %34#0 {handshake.bb = 2 : ui32, handshake.name = "extui12"} : <i2> to <i4>
    %36 = extui %34#2 {handshake.bb = 2 : ui32, handshake.name = "extui13"} : <i2> to <i64>
    %result_2, %index_3 = control_merge [%20, %trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %37:5 = fork [5] %index_3 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %41 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i64} : <>, <i64>
    %42:2 = fork [2] %41 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i64>
    %43 = shli %32, %42#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %44 = trunci %43 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i4>
    %45 = addi %31, %44 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i4>
    %46 = addi %45, %23 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i4>
    %addressResult, %dataResult = load[%46] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i32>, <i4>, <i32>
    %47 = shli %36, %42#0 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %48 = trunci %47 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i4>
    %49 = addi %35, %48 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i4>
    %50 = addi %49, %24 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i4>
    %addressResult_4, %dataResult_5 = load[%50] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i4>, <i32>, <i4>, <i32>
    %51 = addi %dataResult, %dataResult_5 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %52 = addi %27, %51 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %53 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i3>
    %54:2 = fork [2] %53 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i3>
    %55 = trunci %54#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i3> to <i2>
    %56 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 3 : i3} : <>, <i3>
    %57 = cmpi ult, %54#1, %56 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i3>
    %58:6 = fork [6] %57 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult, %falseResult = cond_br %58#0, %55 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink1"} : <i2>
    %trueResult_6, %falseResult_7 = cond_br %58#4, %52 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %58#3, %28 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i2>
    %trueResult_10, %falseResult_11 = cond_br %58#1, %30#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    sink %falseResult_11 {handshake.name = "sink2"} : <i2>
    %trueResult_12, %falseResult_13 = cond_br %58#2, %34#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i2>
    sink %falseResult_13 {handshake.name = "sink3"} : <i2>
    %trueResult_14, %falseResult_15 = cond_br %58#5, %result_2 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %59 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %60 = merge %falseResult_9 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i2>
    %61 = extui %60 {handshake.bb = 3 : ui32, handshake.name = "extui14"} : <i2> to <i3>
    %62 = constant %64 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i3} : <>, <i3>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink4"} : <i1>
    %63 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %64 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %65 = addi %61, %62 {handshake.bb = 3 : ui32, handshake.name = "addi6"} : <i3>
    %66:2 = fork [2] %65 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i3>
    %67 = trunci %66#0 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i3> to <i2>
    %68 = constant %63 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 3 : i3} : <>, <i3>
    %69 = cmpi ult, %66#1, %68 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i3>
    %70:3 = fork [3] %69 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %70#1, %59 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %70#0, %67 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i2>
    sink %falseResult_21 {handshake.name = "sink5"} : <i2>
    %trueResult_22, %falseResult_23 = cond_br %70#2, %result_16 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %71 = merge %falseResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_25 {handshake.name = "sink6"} : <i1>
    %72:2 = fork [2] %result_24 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %71, %memEnd, %0#2 : <i32>, <>, <>
  }
}

