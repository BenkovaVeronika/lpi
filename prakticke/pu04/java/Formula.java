import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public interface Formula {
    public Formula[] subf();

    public String toString();

    public boolean equals(Formula other);

    public Set<String> vars();

    public Cnf toCnf();
}

class Variable implements Formula {
    private static int newNum = 0;
    private String name;

    Variable(String name) {
        this.name = name;
    }

    public String name() {
        return name;
    }

    public Formula[] subf() {
        return new Formula[]{};
    }

    public String toString() {
        return name();
    }

    public boolean equals(Formula other) {
        if (this == other) return true;
        if (getClass() != other.getClass()) return false;
        Variable otherVar = (Variable) other;
        return name().equals(otherVar.name());
    }

    public Set<String> vars() {
        return new HashSet<String>(Arrays.asList(name()));
    }

    /**
     * @return a new variable name that is not used
     */
    public static String newName() {
        // Yes, this is a hack, but this is
        // guaranteed to be unique in our tests ;-)
        return "_x" + ++newNum;
    }

    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        cnf.add(new Clause(new Literal(name)));
        return cnf;
    }
}

class CompositeFormula implements Formula {
    Formula[] subs;
    String conn;

    CompositeFormula(Formula[] subs, String conn) {
        this.subs = subs;
        this.conn = conn;
    }

    public Formula[] subf() {
        return subs;
    }

    public String toString() {
        return "("
                + Arrays.stream(this.subf())
                .map(f -> f.toString())
                .collect(Collectors.joining(this.conn))
                + ")"
                ;
    }

    public boolean equals(Formula other) {
        if (this == other) return true;
        if (getClass() != other.getClass()) return false;
        if (subf().length != other.subf().length) return false;
        for (int i = 0; i < subf().length; ++i)
            if (!subf()[i].equals(other.subf()[i])) return false;
        return true;
    }

    public Set<String> vars() {
        Set<String> vs = new HashSet<String>();
        for (Formula f : subf()) {
            vs.addAll(f.vars());
        }
        return vs;
    }

    public Cnf toCnf() {
        return new Cnf();
    }
}

class Negation extends CompositeFormula {
    public Negation(Formula formula) {
        super(new Formula[]{formula}, "-");
    }

    public Formula originalFormula() {
        return subf()[0];
    }

    @Override
    public String toString() {
        return "-" + originalFormula().toString();
    }

    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        String a = Variable.newName();
        Literal l = Literal.Lit(a);
        Clause c = new Clause(l);
        cnf.add(c);
        Cnf cnf2 = originalFormula().toCnf();

        String b = cnf2.remove(0).remove(0).name();
        cnf.addAll(cnf2);
        Literal nota = Literal.Not(a);
        Literal notb = Literal.Not(b);
        Literal yesa = Literal.Lit(a);
        Literal yesb = Literal.Lit(b);
        Clause first = new Clause(nota,notb);
        Clause second = new Clause(yesa,yesb);
        cnf.add(first); cnf.add(second);
        return cnf;
    }
}

class Conjunction extends CompositeFormula {
    public Conjunction(Formula[] formulas) {
        super(formulas, "&");
    }
    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        String a = Variable.newName();
        Literal l = Literal.Lit(a);
        Clause c = new Clause(l);
        Clause c2 = new Clause(Literal.Lit(a));
        cnf.add(c);
        ArrayList<String> vysl = new ArrayList<>();


        for (int i = 0; i < subs.length; i++) {
            Cnf pom = subs[i].toCnf();
            vysl.add(pom.remove(0).remove(0).name());
            cnf.addAll(pom);

        }

        for (int i = 0; i < vysl.size(); i++) {
            Clause kl = new Clause(Literal.Not(a),Literal.Lit(vysl.get(i)));
            cnf.add(kl);

        }

        for (int i = 0; i < vysl.size(); i++) {
            c2.add(Literal.Not(vysl.get(i)));

        }
        cnf.add(c2);

        return cnf;
    }
}

class Disjunction extends CompositeFormula {
    public Disjunction(Formula[] formulas) {
        super(formulas, "|");
    }

    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        String a = Variable.newName();
        Literal l = Literal.Lit(a);
        Clause c = new Clause(l);
        Clause c2 = new Clause(Literal.Not(a));
        cnf.add(c);
        ArrayList<String> vysl = new ArrayList<>();
        for (int i = 0; i < subs.length; i++) {
            Cnf pom = subs[i].toCnf();
            vysl.add(pom.remove(0).remove(0).name());
            cnf.addAll(pom);
        }
        for (int i = 0; i < vysl.size(); i++) {
            Clause kl = new Clause(Literal.Lit(vysl.get(i)),Literal.Not(vysl.get(i)));
            cnf.add(kl);
        }
        for (int i = 0; i < vysl.size(); i++) {
            Clause kk = new Clause(Literal.Lit(a),Literal.Not(vysl.get(i)));
            cnf.add(kk);
            c2.add(Literal.Lit(vysl.get(i)));
        }
        cnf.add(c2);
        return cnf;
    }
}

class BinaryFormula extends CompositeFormula {
    BinaryFormula(Formula leftSide, Formula rightSide, String conn) {
        super(new Formula[]{leftSide, rightSide}, conn);
    }

    public Formula leftSide() {
        return subf()[0];
    }

    public Formula rightSide() {
        return subf()[1];
    }
}

class Implication extends BinaryFormula {
    public Implication(Formula a, Formula b) {
        super(a, b, "->");
    }

    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        String a = Variable.newName();
        Literal l = Literal.Lit(a);
        Clause c = new Clause(l);
        cnf.add(c);
        Cnf left = leftSide().toCnf();
        String le = left.remove(0).remove(0).name();
        cnf.addAll(left);
        Cnf rajt = rightSide().toCnf();
        String r = rajt.remove(0).remove(0).name();
        cnf.addAll(rajt);

        Clause prvy = new Clause(Literal.Not(a),Literal.Not(le),Literal.Lit(r));
        Clause druhy = new Clause(Literal.Lit(le),Literal.Lit(a));
        Clause treti = new Clause(Literal.Not(r),Literal.Lit(a));
        cnf.add(prvy);cnf.add(druhy);cnf.add(treti);


        return cnf;
    }
}

class Equivalence extends BinaryFormula {
    public Equivalence(Formula a, Formula b) {
        super(a, b, "<->");
    }

    @Override
    public Cnf toCnf() {
        Cnf cnf = new Cnf();
        String a = Variable.newName();
        Literal l = Literal.Lit(a);
        Clause c = new Clause(l);
        cnf.add(c);
        Cnf left = leftSide().toCnf();
        String le = left.remove(0).remove(0).name();
        cnf.addAll(left);
        Cnf rajt = rightSide().toCnf();
        String r = rajt.remove(0).remove(0).name();
        cnf.addAll(rajt);

        Clause prvy = new Clause(Literal.Not(a), Literal.Not(le), Literal.Lit(r));
        Clause druhy = new Clause(Literal.Not(a), Literal.Lit(le), Literal.Not(r));
        Clause treti = new Clause(Literal.Lit(a), Literal.Not(le), Literal.Not(r));
        Clause stvrty = new Clause(Literal.Lit(a), Literal.Lit(le), Literal.Lit(r));
        cnf.add(prvy); cnf.add(druhy);cnf.add(treti);cnf.add(stvrty);



        return cnf;
    }
}
