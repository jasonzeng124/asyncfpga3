module {
  handshake.func @share_test_2(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%16, %addressResult, %addressResult_0, %dataResult_1) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3:2 = fork [2] %2 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i1>
    %4 = extui %3#1 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %5 = extui %3#0 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i7>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %7 = mux %14#0 [%5, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %8:4 = fork [4] %7 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i7>
    %9 = extui %8#2 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i7> to <i8>
    %10 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i8} : <>, <i8>
    %11 = extui %8#3 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i7> to <i32>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %13 = mux %14#1 [%4, %trueResult_2] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %14:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %15:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %16 = constant %15#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant20", value = 456784 : i32} : <>, <i32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant21", value = 123456 : i32} : <>, <i32>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %24 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant22", value = 16 : i32} : <>, <i32>
    %25 = source {handshake.bb = 1 : ui32, handshake.name = "source5"} : <>
    %26 = constant %25 {handshake.bb = 1 : ui32, handshake.name = "constant23", value = 15 : i32} : <>, <i32>
    %27:2 = fork [2] %26 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %28 = source {handshake.bb = 1 : ui32, handshake.name = "source6"} : <>
    %29 = constant %28 {handshake.bb = 1 : ui32, handshake.name = "constant24", value = 14 : i32} : <>, <i32>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %31 = source {handshake.bb = 1 : ui32, handshake.name = "source7"} : <>
    %32 = constant %31 {handshake.bb = 1 : ui32, handshake.name = "constant25", value = 13 : i32} : <>, <i32>
    %33 = source {handshake.bb = 1 : ui32, handshake.name = "source8"} : <>
    %34 = constant %33 {handshake.bb = 1 : ui32, handshake.name = "constant26", value = 9 : i32} : <>, <i32>
    %35 = source {handshake.bb = 1 : ui32, handshake.name = "source9"} : <>
    %36 = constant %35 {handshake.bb = 1 : ui32, handshake.name = "constant27", value = 6 : i32} : <>, <i32>
    %37 = source {handshake.bb = 1 : ui32, handshake.name = "source10"} : <>
    %38 = constant %37 {handshake.bb = 1 : ui32, handshake.name = "constant28", value = 18 : i32} : <>, <i32>
    %39 = source {handshake.bb = 1 : ui32, handshake.name = "source11"} : <>
    %40 = constant %39 {handshake.bb = 1 : ui32, handshake.name = "constant29", value = 17 : i32} : <>, <i32>
    %41 = source {handshake.bb = 1 : ui32, handshake.name = "source12"} : <>
    %42 = constant %41 {handshake.bb = 1 : ui32, handshake.name = "constant30", value = 11 : i32} : <>, <i32>
    %43 = source {handshake.bb = 1 : ui32, handshake.name = "source13"} : <>
    %44 = constant %43 {handshake.bb = 1 : ui32, handshake.name = "constant31", value = 4 : i32} : <>, <i32>
    %45 = source {handshake.bb = 1 : ui32, handshake.name = "source14"} : <>
    %46 = constant %45 {handshake.bb = 1 : ui32, handshake.name = "constant32", value = 3 : i32} : <>, <i32>
    %47 = source {handshake.bb = 1 : ui32, handshake.name = "source15"} : <>
    %48 = constant %47 {handshake.bb = 1 : ui32, handshake.name = "constant33", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %49:14 = fork [14] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %50 = addi %13, %12#0 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %51 = addi %50, %22 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %52:3 = fork [3] %51 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %53 = muli %52#2, %12#1 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %54 = muli %53, %20 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %55 = shli %49#0, %36 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %56 = shli %49#1, %34 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %57 = shli %49#2, %32 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %58 = addi %56, %57 {handshake.bb = 1 : ui32, handshake.name = "addi5"} : <i32>
    %59 = addi %55, %58 {handshake.bb = 1 : ui32, handshake.name = "addi6"} : <i32>
    %60 = shli %49#3, %30#1 {handshake.bb = 1 : ui32, handshake.name = "shli3"} : <i32>
    %61 = shli %49#4, %27#1 {handshake.bb = 1 : ui32, handshake.name = "shli4"} : <i32>
    %62 = shli %49#5, %24 {handshake.bb = 1 : ui32, handshake.name = "shli5"} : <i32>
    %63 = addi %61, %62 {handshake.bb = 1 : ui32, handshake.name = "addi7"} : <i32>
    %64 = addi %60, %63 {handshake.bb = 1 : ui32, handshake.name = "addi8"} : <i32>
    %65 = addi %59, %64 {handshake.bb = 1 : ui32, handshake.name = "addi9"} : <i32>
    %66 = muli %65, %12#2 {handshake.bb = 1 : ui32, handshake.name = "muli3"} : <i32>
    %67 = addi %54, %66 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %68 = shli %49#6, %48 {handshake.bb = 1 : ui32, handshake.name = "shli6"} : <i32>
    %69 = shli %49#7, %46 {handshake.bb = 1 : ui32, handshake.name = "shli7"} : <i32>
    %70 = addi %68, %69 {handshake.bb = 1 : ui32, handshake.name = "addi10"} : <i32>
    %71 = shli %49#8, %44 {handshake.bb = 1 : ui32, handshake.name = "shli8"} : <i32>
    %72 = shli %49#9, %42 {handshake.bb = 1 : ui32, handshake.name = "shli9"} : <i32>
    %73 = addi %71, %72 {handshake.bb = 1 : ui32, handshake.name = "addi11"} : <i32>
    %74 = addi %70, %73 {handshake.bb = 1 : ui32, handshake.name = "addi12"} : <i32>
    %75 = shli %49#10, %30#0 {handshake.bb = 1 : ui32, handshake.name = "shli10"} : <i32>
    %76 = shli %49#11, %27#0 {handshake.bb = 1 : ui32, handshake.name = "shli11"} : <i32>
    %77 = addi %75, %76 {handshake.bb = 1 : ui32, handshake.name = "addi13"} : <i32>
    %78 = shli %49#12, %40 {handshake.bb = 1 : ui32, handshake.name = "shli12"} : <i32>
    %79 = shli %49#13, %38 {handshake.bb = 1 : ui32, handshake.name = "shli13"} : <i32>
    %80 = addi %78, %79 {handshake.bb = 1 : ui32, handshake.name = "addi14"} : <i32>
    %81 = addi %77, %80 {handshake.bb = 1 : ui32, handshake.name = "addi15"} : <i32>
    %82 = addi %74, %81 {handshake.bb = 1 : ui32, handshake.name = "addi16"} : <i32>
    %83 = muli %82, %52#1 {handshake.bb = 1 : ui32, handshake.name = "muli5"} : <i32>
    %84 = addi %67, %83 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_0, %dataResult_1 = store[%8#0] %84 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %85 = addi %9, %10 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i8>
    %86:2 = fork [2] %85 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i8>
    %87 = trunci %86#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %88 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 100 : i8} : <>, <i8>
    %89 = cmpi ult, %86#1, %88 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i8>
    %90:3 = fork [3] %89 {handshake.bb = 1 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult, %falseResult = cond_br %90#0, %87 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_2, %falseResult_3 = cond_br %90#1, %52#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %90#2, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink2"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}

