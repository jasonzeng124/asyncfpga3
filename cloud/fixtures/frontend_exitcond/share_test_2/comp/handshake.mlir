module {
  handshake.func @share_test_2(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%3, %addressResult, %addressResult_0, %dataResult_1) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %4 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%1, %trueResult_2] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant18", value = 100 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant20", value = 456784 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant21", value = 123456 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant22", value = 16 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source5"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant23", value = 15 : i32} : <>, <i32>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source6"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant24", value = 14 : i32} : <>, <i32>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source7"} : <>
    %21 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant25", value = 13 : i32} : <>, <i32>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source8"} : <>
    %23 = constant %22 {handshake.bb = 1 : ui32, handshake.name = "constant26", value = 9 : i32} : <>, <i32>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source9"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant27", value = 6 : i32} : <>, <i32>
    %26 = source {handshake.bb = 1 : ui32, handshake.name = "source10"} : <>
    %27 = constant %26 {handshake.bb = 1 : ui32, handshake.name = "constant28", value = 18 : i32} : <>, <i32>
    %28 = source {handshake.bb = 1 : ui32, handshake.name = "source11"} : <>
    %29 = constant %28 {handshake.bb = 1 : ui32, handshake.name = "constant29", value = 17 : i32} : <>, <i32>
    %30 = source {handshake.bb = 1 : ui32, handshake.name = "source12"} : <>
    %31 = constant %30 {handshake.bb = 1 : ui32, handshake.name = "constant30", value = 11 : i32} : <>, <i32>
    %32 = source {handshake.bb = 1 : ui32, handshake.name = "source13"} : <>
    %33 = constant %32 {handshake.bb = 1 : ui32, handshake.name = "constant31", value = 4 : i32} : <>, <i32>
    %34 = source {handshake.bb = 1 : ui32, handshake.name = "source14"} : <>
    %35 = constant %34 {handshake.bb = 1 : ui32, handshake.name = "constant32", value = 3 : i32} : <>, <i32>
    %36 = source {handshake.bb = 1 : ui32, handshake.name = "source15"} : <>
    %37 = constant %36 {handshake.bb = 1 : ui32, handshake.name = "constant33", value = 2 : i32} : <>, <i32>
    %38 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %39 = trunci %38 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%39] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %40 = addi %5, %4 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %41 = addi %40, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %42 = muli %41, %4 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %43 = muli %42, %11 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %44 = shli %dataResult, %25 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %45 = shli %dataResult, %23 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %46 = shli %dataResult, %21 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %47 = addi %45, %46 {handshake.bb = 1 : ui32, handshake.name = "addi5"} : <i32>
    %48 = addi %44, %47 {handshake.bb = 1 : ui32, handshake.name = "addi6"} : <i32>
    %49 = shli %dataResult, %19 {handshake.bb = 1 : ui32, handshake.name = "shli3"} : <i32>
    %50 = shli %dataResult, %17 {handshake.bb = 1 : ui32, handshake.name = "shli4"} : <i32>
    %51 = shli %dataResult, %15 {handshake.bb = 1 : ui32, handshake.name = "shli5"} : <i32>
    %52 = addi %50, %51 {handshake.bb = 1 : ui32, handshake.name = "addi7"} : <i32>
    %53 = addi %49, %52 {handshake.bb = 1 : ui32, handshake.name = "addi8"} : <i32>
    %54 = addi %48, %53 {handshake.bb = 1 : ui32, handshake.name = "addi9"} : <i32>
    %55 = muli %54, %4 {handshake.bb = 1 : ui32, handshake.name = "muli3"} : <i32>
    %56 = addi %43, %55 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %57 = shli %dataResult, %37 {handshake.bb = 1 : ui32, handshake.name = "shli6"} : <i32>
    %58 = shli %dataResult, %35 {handshake.bb = 1 : ui32, handshake.name = "shli7"} : <i32>
    %59 = addi %57, %58 {handshake.bb = 1 : ui32, handshake.name = "addi10"} : <i32>
    %60 = shli %dataResult, %33 {handshake.bb = 1 : ui32, handshake.name = "shli8"} : <i32>
    %61 = shli %dataResult, %31 {handshake.bb = 1 : ui32, handshake.name = "shli9"} : <i32>
    %62 = addi %60, %61 {handshake.bb = 1 : ui32, handshake.name = "addi11"} : <i32>
    %63 = addi %59, %62 {handshake.bb = 1 : ui32, handshake.name = "addi12"} : <i32>
    %64 = shli %dataResult, %19 {handshake.bb = 1 : ui32, handshake.name = "shli10"} : <i32>
    %65 = shli %dataResult, %17 {handshake.bb = 1 : ui32, handshake.name = "shli11"} : <i32>
    %66 = addi %64, %65 {handshake.bb = 1 : ui32, handshake.name = "addi13"} : <i32>
    %67 = shli %dataResult, %29 {handshake.bb = 1 : ui32, handshake.name = "shli12"} : <i32>
    %68 = shli %dataResult, %27 {handshake.bb = 1 : ui32, handshake.name = "shli13"} : <i32>
    %69 = addi %67, %68 {handshake.bb = 1 : ui32, handshake.name = "addi14"} : <i32>
    %70 = addi %66, %69 {handshake.bb = 1 : ui32, handshake.name = "addi15"} : <i32>
    %71 = addi %63, %70 {handshake.bb = 1 : ui32, handshake.name = "addi16"} : <i32>
    %72 = muli %71, %41 {handshake.bb = 1 : ui32, handshake.name = "muli5"} : <i32>
    %73 = addi %56, %72 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %74 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %75 = trunci %74 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = store[%75] %73 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %76 = addi %4, %9 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %77 = cmpi ne, %76, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %77, %76 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %77, %41 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %77, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %arg2 : <>, <>
  }
}

