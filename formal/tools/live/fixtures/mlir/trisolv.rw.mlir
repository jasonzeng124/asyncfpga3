module {
  handshake.func @trisolv(%arg0: memref<1000xi32>, %arg1: memref<1000000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "A", "c", "x_start", "A_start", "c_start", "start"], resNames = ["x_end", "A_end", "c_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%addressResult) %114#2 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_0:2, %memEnd_1 = mem_controller[%arg1 : memref<1000000xi32>] %arg4 (%addressResult_12, %addressResult_28) %114#1 {connectedBlocks = [2 : i32, 3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i20>, !handshake.channel<i20>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1:4 = lsq[%arg0 : memref<1000xi32>] (%arg3, %8#0, %addressResult_2, %dataResult_3, %26#0, %addressResult_10, %addressResult_14, %addressResult_16, %dataResult_17, %72#0, %addressResult_26, %addressResult_30, %dataResult_31, %114#0)  {groupSizes = [1 : i32, 3 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui11"} : <i1> to <i10>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %index [%4, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %7:4 = fork [4] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %result, %index = control_merge [%5, %trueResult_34]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %9:2 = fork [2] %8#2 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %addressResult, %dataResult = load[%7#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_2, %dataResult_3 = store[%7#0] %dataResult {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    %10 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 0 : i10} : <>, <i10>
    %11 = cmpi ugt, %7#3, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i10>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %13 = constant %9#1 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %12#2, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %14 = extui %trueResult {handshake.bb = 1 : ui32, handshake.name = "extui12"} : <i1> to <i10>
    %trueResult_4, %falseResult_5 = cond_br %12#0, %7#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i10>
    %15 = trunci %falseResult_5 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i10> to <i1>
    %16 = extui %15 {handshake.bb = 1 : ui32, handshake.name = "extui13"} : <i1> to <i10>
    %trueResult_6, %falseResult_7 = cond_br %12#1, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %17 = mux %25#0 [%14, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i10>, <i10>] to <i10>
    %18:3 = fork [3] %17 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i10>
    %19 = extui %18#2 {handshake.bb = 2 : ui32, handshake.name = "extui14"} : <i10> to <i11>
    %20 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i11} : <>, <i11>
    %21 = extui %18#0 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i10> to <i20>
    %22 = mux %25#1 [%trueResult_4, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i10>, <i10>] to <i10>
    %23:5 = fork [5] %22 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i10>
    %24 = extui %23#0 {handshake.bb = 2 : ui32, handshake.name = "extui16"} : <i10> to <i11>
    %result_8, %index_9 = control_merge [%trueResult_6, %trueResult_22]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %25:2 = fork [2] %index_9 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %26:2 = lazy_fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 9 : i64} : <>, <i64>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 8 : i64} : <>, <i64>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 7 : i64} : <>, <i64>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 6 : i64} : <>, <i64>
    %36 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %37 = constant %36 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 5 : i64} : <>, <i64>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source6"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant17", value = 3 : i64} : <>, <i64>
    %addressResult_10, %dataResult_11 = load[%23#2] %1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : <i10>, <i32>, <i10>, <i32>
    %40 = extui %23#4 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i10> to <i64>
    %41:6 = fork [6] %40 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %42 = shli %41#5, %39 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %43 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i20>
    %44 = shli %41#4, %37 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %45 = trunci %44 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i20>
    %46 = shli %41#3, %35 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %47 = trunci %46 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i20>
    %48 = addi %45, %47 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i20>
    %49 = addi %43, %48 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i20>
    %50 = shli %41#2, %33 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %51 = trunci %50 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i64> to <i20>
    %52 = shli %41#1, %31 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %53 = trunci %52 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i64> to <i20>
    %54 = shli %41#0, %29 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %55 = trunci %54 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i64> to <i20>
    %56 = addi %53, %55 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i20>
    %57 = addi %51, %56 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i20>
    %58 = addi %49, %57 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i20>
    %59 = addi %58, %21 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i20>
    %addressResult_12, %dataResult_13 = load[%59] %outputs_0#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i20>, <i32>, <i20>, <i32>
    %addressResult_14, %dataResult_15 = load[%18#1] %1#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load4"} : <i10>, <i32>, <i10>, <i32>
    %60 = muli %dataResult_13, %dataResult_15 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %61 = subi %dataResult_11, %60 {handshake.bb = 2 : ui32, handshake.name = "subi0"} : <i32>
    %addressResult_16, %dataResult_17 = store[%23#1] %61 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : <i10>, <i32>, <i10>, <i32>
    %62 = addi %19, %20 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i11>
    %63:2 = fork [2] %62 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i11>
    %64 = trunci %63#0 {handshake.bb = 2 : ui32, handshake.name = "trunci7"} : <i11> to <i10>
    %65 = cmpi ult, %63#1, %24 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i11>
    %66:3 = fork [3] %65 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %66#0, %64 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i10>
    sink %falseResult_19 {handshake.name = "sink1"} : <i10>
    %trueResult_20, %falseResult_21 = cond_br %66#2, %23#3 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i10>
    %trueResult_22, %falseResult_23 = cond_br %66#1, %26#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %67 = mux %index_25 [%16, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %68:5 = fork [5] %67 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i10>
    %69 = extui %68#0 {handshake.bb = 3 : ui32, handshake.name = "extui17"} : <i10> to <i20>
    %70 = extui %68#3 {handshake.bb = 3 : ui32, handshake.name = "extui18"} : <i10> to <i11>
    %71 = constant %74 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i11} : <>, <i11>
    %result_24, %index_25 = control_merge [%falseResult_7, %falseResult_23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %72:2 = lazy_fork [2] %result_24 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %73 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %74 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %75 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %76 = constant %75 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 9 : i64} : <>, <i64>
    %77 = source {handshake.bb = 3 : ui32, handshake.name = "source10"} : <>
    %78 = constant %77 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 8 : i64} : <>, <i64>
    %79 = source {handshake.bb = 3 : ui32, handshake.name = "source11"} : <>
    %80 = constant %79 {handshake.bb = 3 : ui32, handshake.name = "constant22", value = 7 : i64} : <>, <i64>
    %81 = source {handshake.bb = 3 : ui32, handshake.name = "source12"} : <>
    %82 = constant %81 {handshake.bb = 3 : ui32, handshake.name = "constant23", value = 6 : i64} : <>, <i64>
    %83 = source {handshake.bb = 3 : ui32, handshake.name = "source13"} : <>
    %84 = constant %83 {handshake.bb = 3 : ui32, handshake.name = "constant24", value = 5 : i64} : <>, <i64>
    %85 = source {handshake.bb = 3 : ui32, handshake.name = "source14"} : <>
    %86 = constant %85 {handshake.bb = 3 : ui32, handshake.name = "constant25", value = 3 : i64} : <>, <i64>
    %addressResult_26, %dataResult_27 = load[%68#2] %1#2 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load6"} : <i10>, <i32>, <i10>, <i32>
    %87 = extui %68#4 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i10> to <i64>
    %88:6 = fork [6] %87 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i64>
    %89 = shli %88#5, %86 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %90 = trunci %89 {handshake.bb = 3 : ui32, handshake.name = "trunci8"} : <i64> to <i20>
    %91 = shli %88#4, %84 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %92 = trunci %91 {handshake.bb = 3 : ui32, handshake.name = "trunci9"} : <i64> to <i20>
    %93 = shli %88#3, %82 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %94 = trunci %93 {handshake.bb = 3 : ui32, handshake.name = "trunci10"} : <i64> to <i20>
    %95 = addi %92, %94 {handshake.bb = 3 : ui32, handshake.name = "addi9"} : <i20>
    %96 = addi %90, %95 {handshake.bb = 3 : ui32, handshake.name = "addi10"} : <i20>
    %97 = shli %88#2, %80 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %98 = trunci %97 {handshake.bb = 3 : ui32, handshake.name = "trunci11"} : <i64> to <i20>
    %99 = shli %88#1, %78 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %100 = trunci %99 {handshake.bb = 3 : ui32, handshake.name = "trunci12"} : <i64> to <i20>
    %101 = shli %88#0, %76 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %102 = trunci %101 {handshake.bb = 3 : ui32, handshake.name = "trunci13"} : <i64> to <i20>
    %103 = addi %100, %102 {handshake.bb = 3 : ui32, handshake.name = "addi11"} : <i20>
    %104 = addi %98, %103 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i20>
    %105 = addi %96, %104 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i20>
    %106 = addi %105, %69 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i20>
    %addressResult_28, %dataResult_29 = load[%106] %outputs_0#1 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : <i20>, <i32>, <i20>, <i32>
    %107 = divsi %dataResult_27, %dataResult_29 {handshake.bb = 3 : ui32, handshake.name = "divsi0"} : <i32>
    %addressResult_30, %dataResult_31 = store[%68#1] %107 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store8"} : <i10>, <i32>, <i10>, <i32>
    %108 = addi %70, %71 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i11>
    %109:2 = fork [2] %108 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i11>
    %110 = trunci %109#0 {handshake.bb = 3 : ui32, handshake.name = "trunci14"} : <i11> to <i10>
    %111 = constant %73 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1000 : i11} : <>, <i11>
    %112 = cmpi ult, %109#1, %111 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i11>
    %113:2 = fork [2] %112 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_32, %falseResult_33 = cond_br %113#0, %110 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i10>
    sink %falseResult_33 {handshake.name = "sink2"} : <i10>
    %trueResult_34, %falseResult_35 = cond_br %113#1, %72#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %result_36, %index_37 = control_merge [%falseResult_35]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_37 {handshake.name = "sink3"} : <i1>
    %114:3 = fork [3] %result_36 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#3, %memEnd_1, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

