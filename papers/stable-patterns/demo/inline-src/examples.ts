// The widget's examples: a few of the paper demo's (CHIPDEMO/src/paper/examples.ts), each named in a few words and
// given one line on what its result shows. The programs are the paper demo's, taken from there by id.

export interface Pick {
  readonly id: string;
  readonly name: string;
  readonly line: string;
}

export const PICKS: readonly Pick[] = [
  { id: 'intro', name: 'Constant propagation', line: 'x is 1 on every iteration, so the parameter is not passed.' },
  { id: 'numbering', name: 'Value numbering', line: 'a and b are equal on every call, so b is not passed and a + (a - b) is a.' },
  { id: 'unbox', name: 'Unboxing', line: 'The pair’s second field is always u: the pair is never built, and only its first field is passed.' },
  { id: 'all', name: 'All at once', line: 'On every call a is u, x is 1 and q is Some((s, u)): loop keeps only i and the pair’s first field.' },
  { id: 'app', name: 'A closure disappears', line: 'app is only passed the closure λ₁⟨u⟩, so its call f(1) is known and no closure is built.' },
  { id: 'fold-once', name: 'A fold', line: 'fold is always passed scale⟨c⟩ and the same n, so f(s, i) is known and fold keeps only s and i.' },
  { id: 'stream', name: 'A stream', line: 'g is always a from closure: sum keeps only the counter it captures, and no closure or pair is built.' },
  { id: 'escape', name: 'An escape', line: 'The closure escapes to callers the program does not know, so it stays, capturing the pair’s two fields instead of the pair.' },
  { id: 'stack', name: 'The stack frame', line: 'sum is called with ret and with after⟨n, r⟩, so its pattern leaves r open and the program stays as it is.' },
];
