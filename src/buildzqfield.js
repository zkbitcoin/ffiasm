#!/usr/bin/env node

const bigInt=require("big-integer");
const fs = require("fs");
const path = require("path");
const util = require("util");
const renderFile = util.promisify(require("ejs").renderFile);

const runningAsScript = !module.parent;

const montgomeryBuilder = require("./montgomerybuilder");
const armBuilder = require("./armbuilder");

class ZqBuilder {
    constructor(q, name, no_adx, hpp, element_hpp) {
        const self = this;
        this.q=bigInt(q);
        this.n64 = Math.floor((this.q.bitLength() - 1) / 64)+1;
        this.canOptimizeConsensys = this.q.shiftRight((this.n64-1)*64).leq( bigInt.one.shiftLeft(64).minus(1).shiftRight(1).minus(1) );
        this.name = name;
        this.no_adx = no_adx;
        this.hpp = hpp;
        this.element_hpp = element_hpp;
        this.bigInt = bigInt;
        this.lastTmp=0;
        this.global = {};
        this.global.tmpLabel = function(label) {
            self.lastTmp++;
            label = label || "tmp";
            return label+"_"+self.lastTmp;
        };
        this.montgomeryBuilder = montgomeryBuilder;
        this.armBuilder = armBuilder;
    }

    constantElement(v) {
        let S = "";
        const mask = bigInt("FFFFFFFFFFFFFFFF", 16);
        for (let i=0; i<this.n64; i++) {
            if (i>0) S = S+",";
            let shex = v.shiftRight(i*64).and(mask).toString(16);
            while (shex.length <16) shex = "0" + shex;
            S = S + "0x" + shex;
        }
        return S;
    }

}

function is_adx_supported() {

    try {
        const data = fs.readFileSync('/proc/cpuinfo', 'utf8');
        return data.includes('adx');
    } catch (err) {
        return false;
    }
}

async function buildField(q, name, no_adx, hpp_out, element_hpp_out) {

    (no_adx == undefined) ? no_adx = !is_adx_supported() : no_adx = Boolean(no_adx.toLowerCase() === "true");
    const builder = new ZqBuilder(q, name, no_adx, hpp_out, element_hpp_out);
    let asm = await renderFile(path.join(__dirname, "fr.asm.ejs"), builder, "{no_adx : " + no_adx + "}");
    const cpp = await renderFile(path.join(__dirname, "fr.cpp.ejs"), builder);
    const hpp = await renderFile(path.join(__dirname, "fr.hpp.ejs"), builder);
    const element_hpp = await renderFile(path.join(__dirname, "fr_element.hpp.ejs"), builder);
    const generic_cpp = await renderFile(path.join(__dirname, "fr_generic.cpp.ejs"), builder);
    const raw_generic_cpp = await renderFile(path.join(__dirname, "fr_raw_generic.cpp.ejs"), builder);
    const raw_arm64_s = await renderFile(path.join(__dirname, "fr_raw_arm64.s.ejs"), builder);

    return {asm: asm, hpp: hpp, cpp: cpp, element_hpp: element_hpp, generic_cpp: generic_cpp, raw_generic_cpp: raw_generic_cpp, raw_arm64_s: raw_arm64_s};
}

if (runningAsScript) {
    var argv = require("yargs")
        .usage("Usage: $0 -q [primeNum] -n [name] --no_adx [no_adx] --oc [out .c file] --oh [out .h file] --oa [out .asm file]")
        .demandOption(["q","n"])
        .alias("q", "prime")
        .alias("n", "name")
        .argv;

    const q = bigInt(argv.q);

    const asmFileName =  (argv.oa) ? argv.oa : argv.name.toLowerCase() + ".asm";
    const no_adx =  (argv.no_adx) ? argv.no_adx : undefined;
    const hFileName =  (argv.oh) ? argv.oh : argv.name.toLowerCase() + ".hpp";
    const cFileName =  (argv.oc) ? argv.oc : argv.name.toLowerCase() + ".cpp";
    const hElementFileName =  (argv.oelemh) ? argv.oelemh : argv.name.toLowerCase() + "_element.hpp";
    const cGenericFileName =  (argv.ogenc) ? argv.ogenc : argv.name.toLowerCase() + "_generic.cpp";
    const cRawGenericFileName =  (argv.orawgenc) ? argv.orawgenc : argv.name.toLowerCase() + "_raw_generic.cpp";
    const sRawArm64FileName =  (argv.oarm64s) ? argv.oarm64s : argv.name.toLowerCase() + "_raw_arm64.s";

    buildField(q, argv.name, no_adx, hFileName, hElementFileName).then( (res) => {
        fs.writeFileSync(asmFileName, res.asm, "utf8");
        fs.writeFileSync(hFileName, res.hpp, "utf8");
        fs.writeFileSync(cFileName, res.cpp, "utf8");
        fs.writeFileSync(hElementFileName, res.element_hpp, "utf8");
        fs.writeFileSync(cGenericFileName, res.generic_cpp, "utf8");
        fs.writeFileSync(cRawGenericFileName, res.raw_generic_cpp, "utf8");
        fs.writeFileSync(sRawArm64FileName, res.raw_arm64_s, "utf8");
    });

} else {
    module.exports = buildField;
}
