abstract sig Entry {
    parent: lone Dir
}

sig File extends Entry {}

sig Dir extends Entry {}

one sig Root extends Dir {}

fact RootHasNoParent {
    no Root.parent
}

fact EveryNonRootHasOneParent {
    all e: Entry - Root | one e.parent
}

fact NoCycles {
    all e: Entry | e not in e.^parent
}

fact EveryEntryReachesRoot {
    all e: Entry | Root in e.*parent
}

fact MaxThreeDirectChildren {
    all d: Dir | #(d.~parent) <= 3
}

pred FileAtDepthThree {
    some f: File |
        Root in f.(parent.parent.parent)
}

pred DirectoryWithTwoFiles {
    some d: Dir |
        #(d.~parent & File) = 2
}

pred DirectoryWithAtLeastThreeFiles {
    some d: Dir |
        #(d.*(~parent) & File) >= 3
}

assert EveryNonRootHasRootAncestor {
    all e: Entry - Root |
        Root in e.^parent
}

assert NoMutualAncestry {
    all disj a, b: Entry |
        (a in b.^parent) implies
        (b not in a.^parent)
}

assert SubtreeHasAtMostThreeFiles {
    all d: Dir |
        #(d.~parent) <= 3 implies
        #(d.*(~parent) & File) <= 3
}

run FileAtDepthThree for 6
run DirectoryWithTwoFiles for 6
run DirectoryWithAtLeastThreeFiles for 6

check EveryNonRootHasRootAncestor for 6
check NoMutualAncestry for 6
check SubtreeHasAtMostThreeFiles for 6
