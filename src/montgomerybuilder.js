const bigInt = require("big-integer");
const AsmBuilder = require("./asmbuilder");

// Important Documentation:
// https://www.microsoft.com/en-us/research/wp-content/uploads/1998/06/97Acar.pdf
// https://hackmd.io/@zkteam/modular_multiplication#Benchmarks
//

module.exports.buildMul = buildMul;
module.exports.buildMul_no_adx = buildMul_no_adx;
module.exports.buildSquare = buildSquare;
module.exports.buildSquare_no_adx = buildSquare_no_adx;
module.exports.buildMul1 = buildMul1;
module.exports.buildFromMontgomery = buildFromMontgomery;
module.exports.buildFromMontgomery_no_adx = buildFromMontgomery_no_adx

function templateMontgomery(fn, q, upperLoop) {


    const n64 = Math.floor((q.bitLength() - 1) / 64)+1;
    const canOptimizeConsensys = q.shiftRight((n64-1)*64).leq( bigInt.one.shiftLeft(64).minus(1).shiftRight(1).minus(1) );
    const base = bigInt.one.shiftLeft(64);
    const np64 = base.minus(q.modInv(base));
    const t=4;

    const params = {q, n64, t, canOptimizeConsensys};


    const c = new AsmBuilder(fn, 4 + n64 + 1 + (canOptimizeConsensys ? 0 : 1));

    c.op("mov","rcx","rdx");   // rdx is needed for multiplications so keep it in cx

    // c.op("mov", 2, `0x${np64.toString(16)}`);
    c.op("mov", 2, "[ np ]");
    c.op("xor", 3, 3);

    c.code.push("");
    for (let i=0; i<n64; i++) {

        upperLoop(c, params, i);

        c.code.push("; SecondLoop");
        c.op("mov", "rdx", 2);
        c.op("mulx", 0, "rdx", t);
        c.op("mulx", 1, 0, "[q]");
        c.op("adcx", 0, t);
        for (let j=1; j<n64; j++) {
            c.op("mulx", (j+1)%2, t+j-1, `[q +${j*8}]`);
            c.op("adcx", t+j-1, j%2);
            c.op("adox", t+j-1, t+j);
        }
        c.op("mov", t+n64-1, 3);
        c.op("adcx", t+n64-1, n64%2);
        c.op("adox", t+n64-1, t+n64);
        if (!canOptimizeConsensys) {
            c.op("mov", t+n64, 3);
            c.op("adcx", t+n64, 3);
            c.op("adox", t+n64, t+n64+1);
        }

        c.code.push("");
    }

    c.code.push(";comparison");
    c.flushWr(false);
    if (!canOptimizeConsensys) {
        c.op("test", t+n64, t+n64);
        c.code.push(`jnz ${fn}_sq`);
    }
    for (let i=n64-1; i>=0; i--) {
        c.op("cmp", t+i, `[q + ${i*8}]`);
        c.code.push(`    jc ${fn}_done`);
        c.code.push(`    jnz ${fn}_sq`);
    }

    c.code.push(fn+ "_sq:");
    c.flushWr(true);
    for (let i=0; i<n64; i++) {
        c.op(i==0 ? "sub" : "sbb", t+i, `[q +${i*8}]`);
    }
    c.flushWr(true);

    c.code.push(fn+ "_done:");
    c.flushWr(true);
    c.wrAssignments = [];
    for (let i=0; i<n64; i++) {
        c.op("mov" ,  `[rdi + ${i*8}]`, t+i);
    }

    return c.getCode();
}


function buildMul(fn, q) {
    return templateMontgomery(fn, q, function mulUpperLoop(c, params, i) {
        const {t, n64, canOptimizeConsensys} = params;
        c.code.push("; FirstLoop");
        c.op("mov","rdx", `[rsi + ${i*8}]`);
        if (i==0) {
            c.op("mulx", 0, t, "[rcx]");
            for (let j=1; j<n64; j++) {
                c.op("mulx", j%2, t+j, `[rcx +${j*8}]`);
                c.op("adcx", t+j, (j-1)%2);
            }
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
                c.op("mov", t+n64+1, 3);
                c.op("adcx", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
            }
        } else {
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
            }
            for (let j=0; j<n64; j++) {
                c.op("mulx", 1, 0, `[rcx +${j*8}]`);
                c.op("adcx", t+j, 0);
                c.op("adox", t+j+1, 1);
            }
            if (!canOptimizeConsensys) {
                c.op("adcx", t+n64, 3);
                c.op("adcx", t+n64+1, 3);
                c.op("adox", t+n64+1, 3);
            } else {
                c.op("adcx", t+n64, 3);
            }
        }
    });
}

/*
//
// This is a try in making a better performance in squaring compared to
// multiplication.
//
// This subrutine works worst because Intel can handle only 2 carries. (We would need four to handle the doublings).
// This forces us to use an extra register (rcx) and some logic for seting up and cumulating the carries.
// The result is that this is 5% slower, so we just use the norml multiplication.

function buildSquare(fn, q) {
    return templateMontgomery(fn, q, function mulUpperLoop(c, params, i) {
        const {t, n64, canOptimizeConsensys} = params;
        c.code.push("; FirstLoop");
        c.op("mov","rdx", `[rsi + ${i*8}]`);
        if (i==0) {
            c.op("mulx", 0, t, "[rsi]");
            c.op("shr", 0, "1");
            c.op("adox", 1,3);  // Clean overflow flag
            for (let j=i+1; j<n64; j++) {
                c.op("mulx", j%2, t+j, `[rsi +${j*8}]`);
                c.op("adox", t+j, (j-1)%2);
                c.op("adcx", t+j, t+j);   // Double and accumulate in overflow carry
            }
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64, 3);
                c.op("adox", t+n64 , (n64-1)%2);
                c.op("adcx", t+n64, t+n64);   // Double and accumulate in overflow carry
                c.op("mov", t+n64+1, 3);
                c.op("adox", t+n64+1, 3);
                c.op("adcx", t+n64+1, t+n64+1);
            } else {
                c.op("mov", t+n64, 3);
                c.op("adox", t+n64 , (n64-1)%2);
                c.op("adcx", t+n64, t+n64);   // Double and accumulate in overflow carry
            }
        } else {
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
            }
            c.op("mulx", 1, 0, `[rsi + ${i*8}]`);
            c.op("adcx", t+i, 0);
            for (let j=i+1; j<n64; j++) {
                c.op("adcx", t+j, 1);  // add the last
                if (j>i+1) {
                    c.op("adox", t+j, "rcx");
                    c.op("mov", "rcx", 3);
                    c.op("adcx", "rcx", 3);
                    c.op("adox", "rcx", 3);
                    c.op("adcx", t+j, 1);  // add the last twice
                    c.op("adcx", "rcx", 3);
                } else {
                    c.op("mov", "rcx", 3);
                    c.op("adcx", "rcx", 3);
                }
                c.op("mulx", 1, 0, `[rsi +${j*8}]`);
                c.op("adcx", t+j, 0);
                c.op("adox", t+j, 0);
            }
            if (i+1 < n64) {
                c.op("adcx", t+n64, "rcx");
                if (!canOptimizeConsensys) {
                    c.op("mov", "rcx", 3);
                    c.op("adcx", "rcx", 3);
                }
                c.op("adcx", t+n64, 1);
                c.op("adox", t+n64, 1);
                if (!canOptimizeConsensys) {
                    c.op("adcx", t+n64+1, "rcx");
                    c.op("adox", t+n64+1, 3);
                }
            } else {
                c.op("adcx", t+n64, 1);
                if (!canOptimizeConsensys) {
                    c.op("adcx", t+n64+1, 3);
                }
            }
        }
    });
}

*/


function buildSquare(fn, q) {
    return templateMontgomery(fn, q, function mulUpperLoop(c, params, i) {
        const {t, n64, canOptimizeConsensys} = params;
        c.code.push("; FirstLoop");
        c.op("mov","rdx", `[rsi + ${i*8}]`);
        if (i==0) {
            c.op("mulx", 0, t, "rdx");
            for (let j=1; j<n64; j++) {
                c.op("mulx", j%2, t+j, `[rsi +${j*8}]`);
                c.op("adcx", t+j, (j-1)%2);
            }
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
                c.op("mov", t+n64+1, 3);
                c.op("adcx", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
            }
        } else {
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
            }
            for (let j=0; j<n64; j++) {
                c.op("mulx", 1, 0, `[rsi +${j*8}]`);
                c.op("adcx", t+j, 0);
                c.op("adox", t+j+1, 1);
            }
            if (!canOptimizeConsensys) {
                c.op("adcx", t+n64, 3);
                c.op("adcx", t+n64+1, 3);
                c.op("adox", t+n64+1, 3);
            } else {
                c.op("adcx", t+n64, 3);
            }
        }
    });
}


function buildMul1(fn, q) {
    return templateMontgomery(fn, q, function mulUpperLoop(c, params, i) {
        const {t, n64, canOptimizeConsensys} = params;
        if (i==0) {
            c.code.push("; FirstLoop");
            c.op("mov","rdx", "rcx");
            c.op("mulx", 0, t, "[rsi]");
            for (let j=1; j<n64; j++) {
                c.op("mulx", j%2, t+j, `[rsi +${j*8}]`);
                c.op("adcx", t+j, (j-1)%2);
            }
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
                c.op("mov", t+n64+1, 3);
                c.op("adcx", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
                c.op("adcx", t+n64 , (n64-1)%2);
            }
        } else {
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
            }
        }
    });
}

function buildFromMontgomery(fn, q) {
    return templateMontgomery(fn, q, function mulUpperLoop(c, params, i) {
        const {t, n64, canOptimizeConsensys} = params;
        if (i==0) {
            c.code.push("; FirstLoop");
            for (let j=0; j<n64; j++) {
                c.op("mov", t+j, `[rsi +${j*8}]`);
            }
            c.op("mov", t+n64, 3);
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            }
        } else {
            if (!canOptimizeConsensys) {
                c.op("mov", t+n64+1, 3);
            } else {
                c.op("mov", t+n64, 3);
            }
        }
    });
}

function templateMontgomery_no_adx(fn, q, round) {

    const n64 = Math.floor((q.bitLength() - 1) / 64)+1;
    const canOptimizeConsensys = q.shiftRight((n64-1)*64).leq( bigInt.one.shiftLeft(64).minus(1).shiftRight(1).minus(1) );
    const c = new AsmBuilder(fn, 4 + n64 + 1 + (canOptimizeConsensys ? 0 : 1));
    const t = 4;

    const params = {q, n64, t, canOptimizeConsensys};


    let r0, r1, r2;
    function setR(step) {
        if ((step % 3) == 0) {
            r0 = "r8";
            r1 = "r9";
            r2 = "r10";
        } else if ((step % 3) == 1) {
            r0 = "r9";
            r1 = "r10";
            r2 = "r8";
        } else {
            r0 = "r10";
            r1 = "r8";
            r2 = "r9";
        }
    }

    c.op("sub","rsp", "" + n64 * 8);

    c.op("mov","rcx","rdx");
    c.op("mov","r11", "[ np ]");
    c.op("xor","r8","r8");
    c.op("xor","r9","r9");
    c.op("xor","r10","r10");
    
    // Main loop
    for (let i=0; i < n64 * 2; i++) {
        setR(i);
        round(c, params, i, r0, r1, r2);
        for (let j = i - 1; j >= 0; j--) { // All ms
            if (((i - j) < n64) && (j < n64)) {
                c.op("mov", "rax", "[rsp + " + j * 8 + "]");
                c.op("mul", "qword [q + " + (i - j) * 8 + "]");
                c.op("add", r0, "rax");
                c.op("adc", r1, "rdx");
                c.op("adc", r2, "0x0");
            }
        } // ms
        if (i < n64) {
            c.op("mov", "rax", r0);
            c.op("mul", "r11");
            c.op("mov", "[rsp + " + i * 8 + "]", "rax");
            c.op("mul", "qword [q]");
            c.op("add", r0, "rax");
            c.op("adc", r1, "rdx");
            c.op("adc", r2, "0x0");
        } else {
            c.op("mov", "[rdi + " + (i - n64) * 8 + "]", r0);
            c.op("xor", r0, r0);
        }
    } // Main Loop

    c.op("test", r1, r1);
    c.code.push("jnz " +  fn + "_mulM_sq");
    c.code.push("; Compare with q");
    for (let i=0; i < n64; i++) {
        c.op("mov", "rax", "[rdi + " + (n64 - i - 1) * 8 + "]");
        c.op("cmp", "rax", "[q + " + (n64 - i -1) * 8 + "]");
        c.code.push("jc " + fn + "_mulM_done") ;         // q is bigget so done.
        c.code.push("jnz " + fn + "_mulM_sq");          //  q is lower
    }

    c.code.push("; If equal subtract q")

    c.code.push(fn + "_mulM_sq:");

    for (let i=0; i < n64; i++) {
        c.op("mov", "rax", "[q + " + i * 8 + "]");
        if (i == 0) {
            c.op("sub", "[rdi + " + i * 8 + "]", "rax");
        } else {
            c.op("sbb", "[rdi + " + i * 8 + "]", "rax");
        }
    }

    c.code.push(fn + "_mulM_done:");

    c.code.push("; Deallocate the reserved space on the stack");

    c.op("add", "rsp", "" + n64 * 8); // Restore stack pointer to deallocate memory

    c.flushWr(true);

    return c.getCode();

}

function buildMul_no_adx(fn, q) {
    return templateMontgomery_no_adx(fn, q, function(c, params, i, r0, r1, r2) {
        const {n64} = params;
        // Same Digit
        for (let o1 = Math.max(0, i - n64+1); (o1 <= i) && (o1 < n64); o1++) {
            const o2= i-o1;
            c.op("mov", "rax", "[rsi + " + 8 * o1 + "]")
            c.op("mul", "qword [rcx + " + 8 * o2 + "]")
            c.op("add", r0, "rax")
            c.op("adc", r1, "rdx")
            c.op("adc", r2, "0x0")
        } // Same digit
    });
}

function buildSquare_no_adx(fn, q) {
    return templateMontgomery_no_adx(fn, q, function(c, params, i, r0, r1, r2) {
        const {n64} = params;
        // Same Digit
        for (let o1 = Math.max(0, i - n64 +1); (o1 < ((i+1) >> 1) ) && (o1 < n64); o1++) {
            const o2= i-o1;
            c.op("mov", "rax", "[rsi + "  + 8 * o1 + "]")
            c.op("mul", "qword [rsi + " + 8 * o2 + "]")
            c.op("add", r0, "rax")
            c.op("adc", r1, "rdx")
            c.op("adc", r2, "0x0")
            c.op("add", r0, "rax")
            c.op("adc", r1, "rdx")
            c.op("adc", r2, "0x0")
        } // Same digit
        if (i % 2 == 0) {
            c.op("mov", "rax", "[rsi + " + 8 * (i/2) + "]")
            c.op("mul", "rax")
            c.op("add", r0, "rax")
            c.op("adc", r1, "rdx")
            c.op("adc", r2, "0x0")
        }
    });
}

function buildFromMontgomery_no_adx(fn, q) {
    return templateMontgomery_no_adx(fn, q, function(c, params, i, r0, r1, r2) {
        const {n64} = params;
        // Same Digit
        if (i<n64) {
            c.op("add", r0, "[rsi + " + 8 * i + "]")
            c.op("adc", r1, "0x0")
            c.op("adc", r2, "0x0")
        } // Same digit
    });
}

// const code = buildMontgomeryMul("Fr_rawMul", bigInt("21888242871839275222246405745257275088548364400416034343698204186575808495617"));
// const code = buildMontgomeryMul("Fr_rawMul", bigInt("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F", 16));
// const code = buildMontgomeryMul("Fr_rawMul", bigInt("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787"));


// const code = buildMontgomeryMul("Fr_rawMul", bigInt("41898490967918953402344214791240637128170709919953949071783502921025352812571106773058893763790338921418070971888458477323173057491593855069696241854796396165721416325350064441470418137846398469611935719059908164220784476160001"));



// console.log(code);




/*
mulx    rax, <%t0>, [rcx + <%=0%>]

mulx    r8, <%t1>, [rcx + <%=1%>]
adc     <%t1>, rax

mulx    rax, <%t2>, [rcx + <%=2%>]
adc     <%t2>, r8

mulx    rax, <%t[n-1]>, [rcx + <%=2%>]
adc     <%t[n-1]>, r8

adc     rax, 0
mov     <%t[n]>, rax

...if(bigPrime)  adc, <%t[n+1]%>, 0

// Subsequent
mulx    rax, r8, [rcx + <%=0%>]
adcx     <%t[0]>, r8
adox     <%t[1]>, rax

mulx    rax, r8, [rcx + <%=0%>]
adcx     <%t[1]>, r8
adox     <%t[2]>, rax
.
.
mulx    rax, r8, [rcx + <%=0%>]
adcx     <%t[n-1]>, r8
adox     <%t[n]>, rax

adcx     <%t[n]>, 0
...ifBigPrime a   adox <%t[n+1]>, 0
*/

