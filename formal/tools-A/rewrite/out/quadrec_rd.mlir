module {
  handshake.func @quadrec(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["x", "n", "start"], resNames = ["out0", "end"]} {
    %0:7 = fork [7] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = constant %0#5 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = -1150833019 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:7 = fork [7] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i32>
    %8 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = -59837582 : i27} : <>, <i27>
    %trueResult_0, %falseResult_1 = cond_br %5#1, %8 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i27>
    %9 = extsi %falseResult_1 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i27> to <i30>
    %10 = extsi %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i27> to <i30>
    %11 = extui %9 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i30> to <i32>
    %12 = extui %10 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i30> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#6, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %13 = constant %0#2 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = -368449945 : i30} : <>, <i30>
    %trueResult_4, %falseResult_5 = cond_br %5#2, %13 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i30>
    %14 = extsi %falseResult_5 {handshake.bb = 0 : ui32, handshake.name = "extsi2"} : <i30> to <i31>
    %15 = extsi %trueResult_4 {handshake.bb = 0 : ui32, handshake.name = "extsi3"} : <i30> to <i31>
    %16 = extui %14 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i31> to <i32>
    %17 = extui %15 {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i31> to <i32>
    %trueResult_6, %falseResult_7 = cond_br %5#5, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %5#4, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink1"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %5#3, %0#4 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %18 = mux %28#0 [%7, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %28#1 [%12, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %21 = mux %28#2 [%trueResult_2, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %28#3 [%17, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %23:2 = fork [2] %22 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %24 = mux %28#4 [%trueResult_6, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %25:2 = fork [2] %24 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %rd0ds = source {handshake.bb = 1 : ui32, handshake.name = "sourcerd0d"} : <>
    %rd0dc = constant %rd0ds {handshake.bb = 1 : ui32, handshake.name = "constantrd0d", value = -1 : i32} : <>, <i32>
    %rd0dd = addi %trueResult_8, %rd0dc {handshake.bb = 1 : ui32, handshake.name = "addird0d"} : <i32>
    %26 = mux %28#5 [%rd0dd, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %27:2 = fork [2] %26 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i32>
    %result, %index = control_merge [%trueResult_10, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %28:6 = fork [6] %index {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <i1>
    %29 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %30 = constant %29 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %31 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %32 = constant %31 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 3 : i32} : <>, <i32>
    %33 = xori %23#1, %25#1 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %34 = addi %21, %33 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %35 = shrui %20#1, %32 {handshake.bb = 1 : ui32, handshake.name = "shrui0"} : <i32>
    %36 = addi %34, %35 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %rd0f:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "forkrd0f"} : <i32>
    %37 = addi %rd0f#0, %30 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %rd0i:2 = fork [2] %rd0f#1 {handshake.bb = 1 : ui32, handshake.name = "forkrd0i"} : <i32>
    %rd0m:2 = fork [2] %27#1 {handshake.bb = 1 : ui32, handshake.name = "forkrd0m"} : <i32>
    %rd0lt = cmpi slt, %rd0i#0, %rd0m#0 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %rd0s1 = source {handshake.bb = 1 : ui32, handshake.name = "sourcerd0a"} : <>
    %rd0k1 = constant %rd0s1 {handshake.bb = 1 : ui32, handshake.name = "constantrd0a", value = 2147483647 : i32} : <>, <i32>
    %rd0s2 = source {handshake.bb = 1 : ui32, handshake.name = "sourcerd0b"} : <>
    %rd0k2 = constant %rd0s2 {handshake.bb = 1 : ui32, handshake.name = "constantrd0b", value = 2147483647 : i32} : <>, <i32>
    %rd0ei = cmpi eq, %rd0i#1, %rd0k1 {handshake.bb = 1 : ui32, handshake.name = "cmpird0i"} : <i32>
    %rd0em = cmpi eq, %rd0m#1, %rd0k2 {handshake.bb = 1 : ui32, handshake.name = "cmpird0m"} : <i32>
    %rd0x = xori %rd0lt, %rd0ei {handshake.bb = 1 : ui32, handshake.name = "xorird0a"} : <i1>
    %39 = xori %rd0x, %rd0em {handshake.bb = 1 : ui32, handshake.name = "xorird0b"} : <i1>
    %40:7 = fork [7] %39 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %40#6, %37 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink2"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %40#5, %36 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %40#4, %23#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %40#3, %25#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %40#2, %20#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %40#1, %27#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_23 {handshake.name = "sink3"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %40#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %41 = mux %45#0 [%falseResult_7, %falseResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %42 = mux %45#1 [%16, %falseResult_19] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %43 = mux %45#2 [%falseResult_3, %falseResult_17] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %44 = mux %45#3 [%11, %falseResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_11, %falseResult_25]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %45:4 = fork [4] %index_27 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    sink %result_26 {handshake.name = "sink4"} : <>
    %46 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %47 = constant %46 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %48 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %49 = constant %48 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %50 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %51 = constant %50 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %52 = shli %42, %49 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %53 = shli %41, %47 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %54 = xori %52, %53 {handshake.bb = 2 : ui32, handshake.name = "xori1"} : <i32>
    %55 = shli %44, %51 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %56 = xori %54, %55 {handshake.bb = 2 : ui32, handshake.name = "xori2"} : <i32>
    %57 = xori %56, %43 {handshake.bb = 2 : ui32, handshake.name = "xori3"} : <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %57, %0#3 : <i32>, <>
  }
}

