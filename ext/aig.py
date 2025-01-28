class Aig(object):
    def __init__(self, M, I, L, O, A):
        self._M = M
        self._I = I
        self._L = L
        self._O = O
        self._A = A
        self._Init = None

    @property
    def maxVar(self): return self._M
    @property
    def inSz(self): return self._I
    @property
    def regSz(self): return self._L
    @property
    def outSz(self): return self._O
    @property
    def gateSz(self): return self._A
    @property
    def init(self): return self._Init
    @init.setter
    def init(self, v): self._Init = v

    def __str__(self):
        return 'aag {M} {I} {L} {O} {A}'.format(M=self.maxVar,
                                                I=self.inSz,
                                                L=self.regSz,
                                                O=self.outSz,
                                                A=self.gateSz)


class ParseException(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)


def parse(input):
    header = next(input).split()
    header = [chunk.decode('utf-8') for chunk in header]

    if len(header) < 6:
        raise ParseException("Incorrect header" + str(header))
    if header[0] != 'aig':
        raise ParseException('Not a binary aig file: ' + str(header))

    ntk = Aig(int(header[1]),
              int(header[2]),
              int(header[3]),
              int(header[4]),
              int(header[5]))

    init = list()
    for i in range(ntk.regSz):
        reg = next(input).split()
        reg = [chunk.decode('utf-8') for chunk in reg]
        if len(reg) == 1:
            init.append(0)
        elif reg[1] == '0' or reg[1] == '1':
            init.append(int(reg[1]))
        else:
            init.append(2)
    ntk.init = init

    return ntk


def adjust_cex(in_cex, cex_aig, orig_aig, out_cex):
    res = next(in_cex)
    out_cex.write (res)

    prop = next(in_cex)
    out_cex.write (prop)

    out_cex.flush()
    # adjust if cex aig has more inputs
    adjust = (orig_aig.inSz < cex_aig.inSz)
    extra_inputs = cex_aig.inSz - orig_aig.inSz

    # eat old initial state. We will re-build it using latches in the
    # original ntk
    init = next(in_cex)
    # all cex_aig latches are initialized
    assert (len (init.strip ()) == cex_aig.regSz)

    if adjust:
        # the initial value of the extra inputs is the initial value
        # of the latches
        init = next (in_cex).strip ()
        # additional inputs are the initial values of the dc latches
        dc = (init[orig_aig.inSz:])
    orig = iter(init[0:orig_aig.inSz])

    j = 0

    for i in range (0, orig_aig.regSz):
        v = orig_aig.init [i]
        if v == 2:
            assert (adjust)
            v = dc[j]
            j += 1
        out_cex.write (str (v))
    out_cex.write ('\n')

    if adjust:
        out_cex.write(init[0:orig_aig.inSz])
        out_cex.write('\n')

    for line in in_cex:
        if not adjust or len(line.strip()) != cex_aig.inSz:
            out_cex.write(line)
        else:
            # remove extra inputs
            out_cex.write(line[0:orig_aig.inSz])
            out_cex.write('\n')

        if line.strip() == '.':
            break

    out_cex.flush()


if __name__ == '__main__':
    import sys
    adjust_cex(in_cex=open(sys.argv[1]), cex_aig=parse(open(sys.argv[2])),
               orig_aig=parse(open(sys.argv[3])), out_cex=sys.stdout)
