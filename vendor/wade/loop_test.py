#!/usr/bin/python3

import TMBuilder
from TMBuilder import subroutine

class Test(TMBuilder.TMBuilder):

    @subroutine
    def main(self):
        iterations = self.reg("iterations")
        v_1 = self.reg("v_1")
        scratch = self.reg("scratch")
        return [
            iterations.inc,
            self.while_decnz(iterations, scratch.inc),
            self.while_decnz(scratch, [iterations.inc, v_1.inc]),
                ]

if __name__ == "__main__":
    Test().process_cmdline()
