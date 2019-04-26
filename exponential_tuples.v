Definition foo := fix foo (n : nat) : Type := match n with 0 => nat | S k => let bar : Type := foo k in (bar * bar)%type end.
Definition baz := fix baz (n : nat) : foo n := match n with 0 => 0 | S k => let quux := baz k in (quux, quux) end.
