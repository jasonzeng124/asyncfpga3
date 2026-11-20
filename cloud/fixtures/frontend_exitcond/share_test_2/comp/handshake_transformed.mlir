module {
  handshake.func @share_test_2(%arg0: memref<100xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<100xi32>] %arg1 (%13, %addressResult, %addressResult_0, %dataResult_1) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %4:2 = fork [2] %3 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %11#0 [%4#0, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7:6 = fork [6] %6 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %8 = trunci %7#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %9 = trunci %7#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i7>
    %10 = mux %11#1 [%4#1, %trueResult_2] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%5, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %12:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <>
    %13 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant18", value = 100 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant20", value = 456784 : i32} : <>, <i32>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %21 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant21", value = 123456 : i32} : <>, <i32>
    %22 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %23 = constant %22 {handshake.bb = 1 : ui32, handshake.name = "constant22", value = 16 : i32} : <>, <i32>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source5"} : <>
    %25 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant23", value = 15 : i32} : <>, <i32>
    %26:2 = fork [2] %25 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %27 = source {handshake.bb = 1 : ui32, handshake.name = "source6"} : <>
    %28 = constant %27 {handshake.bb = 1 : ui32, handshake.name = "constant24", value = 14 : i32} : <>, <i32>
    %29:2 = fork [2] %28 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %30 = source {handshake.bb = 1 : ui32, handshake.name = "source7"} : <>
    %31 = constant %30 {handshake.bb = 1 : ui32, handshake.name = "constant25", value = 13 : i32} : <>, <i32>
    %32 = source {handshake.bb = 1 : ui32, handshake.name = "source8"} : <>
    %33 = constant %32 {handshake.bb = 1 : ui32, handshake.name = "constant26", value = 9 : i32} : <>, <i32>
    %34 = source {handshake.bb = 1 : ui32, handshake.name = "source9"} : <>
    %35 = constant %34 {handshake.bb = 1 : ui32, handshake.name = "constant27", value = 6 : i32} : <>, <i32>
    %36 = source {handshake.bb = 1 : ui32, handshake.name = "source10"} : <>
    %37 = constant %36 {handshake.bb = 1 : ui32, handshake.name = "constant28", value = 18 : i32} : <>, <i32>
    %38 = source {handshake.bb = 1 : ui32, handshake.name = "source11"} : <>
    %39 = constant %38 {handshake.bb = 1 : ui32, handshake.name = "constant29", value = 17 : i32} : <>, <i32>
    %40 = source {handshake.bb = 1 : ui32, handshake.name = "source12"} : <>
    %41 = constant %40 {handshake.bb = 1 : ui32, handshake.name = "constant30", value = 11 : i32} : <>, <i32>
    %42 = source {handshake.bb = 1 : ui32, handshake.name = "source13"} : <>
    %43 = constant %42 {handshake.bb = 1 : ui32, handshake.name = "constant31", value = 4 : i32} : <>, <i32>
    %44 = source {handshake.bb = 1 : ui32, handshake.name = "source14"} : <>
    %45 = constant %44 {handshake.bb = 1 : ui32, handshake.name = "constant32", value = 3 : i32} : <>, <i32>
    %46 = source {handshake.bb = 1 : ui32, handshake.name = "source15"} : <>
    %47 = constant %46 {handshake.bb = 1 : ui32, handshake.name = "constant33", value = 2 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%9] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %48:14 = fork [14] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i32>
    %49 = addi %10, %7#5 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %50 = addi %49, %21 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %51:3 = fork [3] %50 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %52 = muli %51#2, %7#4 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %53 = muli %52, %19 {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %54 = shli %48#0, %35 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %55 = shli %48#1, %33 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i32>
    %56 = shli %48#2, %31 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i32>
    %57 = addi %55, %56 {handshake.bb = 1 : ui32, handshake.name = "addi5"} : <i32>
    %58 = addi %54, %57 {handshake.bb = 1 : ui32, handshake.name = "addi6"} : <i32>
    %59 = shli %48#3, %29#1 {handshake.bb = 1 : ui32, handshake.name = "shli3"} : <i32>
    %60 = shli %48#4, %26#1 {handshake.bb = 1 : ui32, handshake.name = "shli4"} : <i32>
    %61 = shli %48#5, %23 {handshake.bb = 1 : ui32, handshake.name = "shli5"} : <i32>
    %62 = addi %60, %61 {handshake.bb = 1 : ui32, handshake.name = "addi7"} : <i32>
    %63 = addi %59, %62 {handshake.bb = 1 : ui32, handshake.name = "addi8"} : <i32>
    %64 = addi %58, %63 {handshake.bb = 1 : ui32, handshake.name = "addi9"} : <i32>
    %65 = muli %64, %7#3 {handshake.bb = 1 : ui32, handshake.name = "muli3"} : <i32>
    %66 = addi %53, %65 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %67 = shli %48#6, %47 {handshake.bb = 1 : ui32, handshake.name = "shli6"} : <i32>
    %68 = shli %48#7, %45 {handshake.bb = 1 : ui32, handshake.name = "shli7"} : <i32>
    %69 = addi %67, %68 {handshake.bb = 1 : ui32, handshake.name = "addi10"} : <i32>
    %70 = shli %48#8, %43 {handshake.bb = 1 : ui32, handshake.name = "shli8"} : <i32>
    %71 = shli %48#9, %41 {handshake.bb = 1 : ui32, handshake.name = "shli9"} : <i32>
    %72 = addi %70, %71 {handshake.bb = 1 : ui32, handshake.name = "addi11"} : <i32>
    %73 = addi %69, %72 {handshake.bb = 1 : ui32, handshake.name = "addi12"} : <i32>
    %74 = shli %48#10, %29#0 {handshake.bb = 1 : ui32, handshake.name = "shli10"} : <i32>
    %75 = shli %48#11, %26#0 {handshake.bb = 1 : ui32, handshake.name = "shli11"} : <i32>
    %76 = addi %74, %75 {handshake.bb = 1 : ui32, handshake.name = "addi13"} : <i32>
    %77 = shli %48#12, %39 {handshake.bb = 1 : ui32, handshake.name = "shli12"} : <i32>
    %78 = shli %48#13, %37 {handshake.bb = 1 : ui32, handshake.name = "shli13"} : <i32>
    %79 = addi %77, %78 {handshake.bb = 1 : ui32, handshake.name = "addi14"} : <i32>
    %80 = addi %76, %79 {handshake.bb = 1 : ui32, handshake.name = "addi15"} : <i32>
    %81 = addi %73, %80 {handshake.bb = 1 : ui32, handshake.name = "addi16"} : <i32>
    %82 = muli %81, %51#1 {handshake.bb = 1 : ui32, handshake.name = "muli5"} : <i32>
    %83 = addi %66, %82 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %addressResult_0, %dataResult_1 = store[%8] %83 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %84 = addi %7#2, %17 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %85:2 = fork [2] %84 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i32>
    %86 = cmpi ne, %85#1, %15 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %87:3 = fork [3] %86 {handshake.bb = 1 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult, %falseResult = cond_br %87#2, %85#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %87#1, %51#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %87#0, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink2"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %0#1 : <>, <>
  }
}

