module {
  func.func @gemm(%arg0: i32 {handshake.arg_name = "alpha"}, %arg1: i32 {handshake.arg_name = "beta"}, %arg2: memref<900xi32> {handshake.arg_name = "A"}, %arg3: memref<900xi32> {handshake.arg_name = "B"}, %arg4: memref<900xi32> {handshake.arg_name = "C"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb4
    %c0_i32_1 = arith.constant {handshake.name = "constant9"} 0 : i32
    %c4_i64 = arith.constant {handshake.name = "constant10"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant11"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant12"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant13"} 1 : i64
    %5 = arith.extui %4 {handshake.name = "extui3"} : i32 to i64
    %6 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %7 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %8 = arith.addi %6, %7 {handshake.name = "addi7"} : i64
    %9 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %10 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi8"} : i64
    %12 = arith.addi %8, %11 {handshake.name = "addi9"} : i64
    %13 = arith.addi %12, %5 {handshake.name = "addi0"} : i64
    %14 = arith.index_cast %13 {handshake.name = "index_cast0"} : i64 to index
    %15 = memref.load %arg4[%14] {handshake.name = "load0"} : memref<900xi32>
    %16 = arith.muli %15, %arg1 {handshake.name = "muli1"} : i32
    %17 = arith.sitofp %16 {handshake.name = "sitofp0"} : i32 to f32
    %18 = arith.extui %4 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb3(%17, %c0_i32_1 : f32, i32) {handshake.name = "br2"}
  ^bb3(%19: f32, %20: i32):  // 2 preds: ^bb2, ^bb3
    %c20_i32 = arith.constant {handshake.name = "constant14"} 20 : i32
    %c1_i32 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c4_i64_2 = arith.constant {handshake.name = "constant16"} 4 : i64
    %c3_i64_3 = arith.constant {handshake.name = "constant17"} 3 : i64
    %c2_i64_4 = arith.constant {handshake.name = "constant18"} 2 : i64
    %c1_i64_5 = arith.constant {handshake.name = "constant19"} 1 : i64
    %21 = arith.extui %20 {handshake.name = "extui5"} : i32 to i64
    %22 = arith.shli %2, %c1_i64_5 {handshake.name = "shli4"} : i64
    %23 = arith.shli %2, %c2_i64_4 {handshake.name = "shli5"} : i64
    %24 = arith.addi %22, %23 {handshake.name = "addi10"} : i64
    %25 = arith.shli %2, %c3_i64_3 {handshake.name = "shli6"} : i64
    %26 = arith.shli %2, %c4_i64_2 {handshake.name = "shli7"} : i64
    %27 = arith.addi %25, %26 {handshake.name = "addi11"} : i64
    %28 = arith.addi %24, %27 {handshake.name = "addi12"} : i64
    %29 = arith.addi %28, %21 {handshake.name = "addi1"} : i64
    %30 = arith.index_cast %29 {handshake.name = "index_cast1"} : i64 to index
    %31 = memref.load %arg2[%30] {handshake.name = "load1"} : memref<900xi32>
    %32 = arith.muli %31, %arg0 {handshake.name = "muli3"} : i32
    %33 = arith.extui %20 {handshake.name = "extui6"} : i32 to i64
    %34 = arith.shli %33, %c1_i64_5 {handshake.name = "shli8"} : i64
    %35 = arith.shli %33, %c2_i64_4 {handshake.name = "shli9"} : i64
    %36 = arith.addi %34, %35 {handshake.name = "addi13"} : i64
    %37 = arith.shli %33, %c3_i64_3 {handshake.name = "shli10"} : i64
    %38 = arith.shli %33, %c4_i64_2 {handshake.name = "shli11"} : i64
    %39 = arith.addi %37, %38 {handshake.name = "addi14"} : i64
    %40 = arith.addi %36, %39 {handshake.name = "addi15"} : i64
    %41 = arith.addi %40, %18 {handshake.name = "addi2"} : i64
    %42 = arith.index_cast %41 {handshake.name = "index_cast2"} : i64 to index
    %43 = memref.load %arg3[%42] {handshake.name = "load2"} : memref<900xi32>
    %44 = arith.muli %32, %43 {handshake.name = "muli5"} : i32
    %45 = arith.sitofp %44 {handshake.name = "sitofp1"} : i32 to f32
    %46 = arith.addf %19, %45 {handshake.name = "addf0"} : f32
    %47 = arith.addi %20, %c1_i32 {handshake.name = "addi3"} : i32
    %48 = arith.cmpi ult, %47, %c20_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %48, ^bb3(%46, %47 : f32, i32), ^bb4(%46 : f32) {handshake.name = "cond_br0"}
  ^bb4(%49: f32):  // pred: ^bb3
    %c20_i32_6 = arith.constant {handshake.name = "constant20"} 20 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant21"} 1 : i32
    %c4_i64_8 = arith.constant {handshake.name = "constant22"} 4 : i64
    %c3_i64_9 = arith.constant {handshake.name = "constant23"} 3 : i64
    %c2_i64_10 = arith.constant {handshake.name = "constant24"} 2 : i64
    %c1_i64_11 = arith.constant {handshake.name = "constant25"} 1 : i64
    %50 = arith.fptosi %49 {handshake.name = "fptosi0"} : f32 to i32
    %51 = arith.extui %4 {handshake.name = "extui7"} : i32 to i64
    %52 = arith.shli %3, %c1_i64_11 {handshake.name = "shli12"} : i64
    %53 = arith.shli %3, %c2_i64_10 {handshake.name = "shli13"} : i64
    %54 = arith.addi %52, %53 {handshake.name = "addi16"} : i64
    %55 = arith.shli %3, %c3_i64_9 {handshake.name = "shli14"} : i64
    %56 = arith.shli %3, %c4_i64_8 {handshake.name = "shli15"} : i64
    %57 = arith.addi %55, %56 {handshake.name = "addi17"} : i64
    %58 = arith.addi %54, %57 {handshake.name = "addi18"} : i64
    %59 = arith.addi %58, %51 {handshake.name = "addi4"} : i64
    %60 = arith.index_cast %59 {handshake.name = "index_cast3"} : i64 to index
    memref.store %50, %arg4[%60] {handshake.name = "store3"} : memref<900xi32>
    %61 = arith.addi %4, %c1_i32_7 {handshake.name = "addi5"} : i32
    %62 = arith.cmpi ult, %61, %c20_i32_6 {handshake.name = "cmpi1"} : i32
    cf.cond_br %62, ^bb2(%61 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c20_i32_12 = arith.constant {handshake.name = "constant26"} 20 : i32
    %c1_i32_13 = arith.constant {handshake.name = "constant27"} 1 : i32
    %63 = arith.addi %0, %c1_i32_13 {handshake.name = "addi6"} : i32
    %64 = arith.cmpi ult, %63, %c20_i32_12 {handshake.name = "cmpi2"} : i32
    cf.cond_br %64, ^bb1(%63 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}

