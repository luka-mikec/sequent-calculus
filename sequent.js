/*
    sequent:
        ante: [formula]
        succ: [formula]

        left: sequent
        right: sequent

 */

class sequent {
    constructor()
    {
        this.ante = [];
        this.succ = [];
        this.left = null;
        this.right = null;
    }

    text_print(indent) {
        if (!indent) indent = 0;

        return "  ".repeat(indent) + this.ante.map(f => html_str_formula(f)).join(", ") +
            " ---> " + this.succ.map(f => html_str_formula(f)).join(", ") + "\n" +
            (this.left ? this.left.print(indent + 2) : "") +
            (this.right ? this.right.print(indent + 2) : "");
    }

    latex_print(out) {
        let str_formula = latex_str_formula;

        let init = !out;
        if (init)
        {
            out = {};
            out.val = ` % this is LaTeX output for use with bussproofs.sty (https://www.math.ucsd.edu/~sbuss/ResearchWeb/bussproofs/bussproofs.sty)
\\begin{prooftree}
`;
        }

        let me_latex = this.ante.map(f => str_formula(f)).join(", ") +
            "  \\longrightarrow  " + this.succ.map(f => str_formula(f)).join(", ");

        if (!this.left && !this.right)
        {
            out.val += `\\AxiomC{\$ ${ me_latex } \$}\n`;
            return;
        }

        if (this.left) this.left.latex_print(out);
        if (this.right) this.right.latex_print(out);


        if (this.left && !this.right)
            out.val += `\\UnaryInfC{\$ ${ me_latex } \$}\n`;
        if (this.left && this.right)
            out.val += `\\BinaryInfC{\$ ${ me_latex } \$}\n`;

        if (init)
        {
            out.val += `\\end{prooftree}`;
            return out.val;
        }
    }

    print() {
        let str_formula = html_str_formula;

        return this.ante.map(f => str_formula(f)).join(", ") +
            "  ⟹  " + this.succ.map(f => str_formula(f)).join(", ");
    }

    html_print() {


        let me = document.createElement('div');
        me.className = 'gentz_node';

        let me_html = this.print();


        let me_as_co = document.createElement('div');
        me_as_co.className = 'gentz_as_co';
        me.appendChild(me_as_co);

        if (!this.left && !this.right) {
            let me_st_as =  document.createElement('div');
            me_st_as.className = 'gentz_init_as';
            me_st_as.innerText = me_html;
            me_as_co.appendChild(me_st_as);

            return me;
        }

        let me_as = document.createElement('div');
        me_as.className = 'gentz_as';
        me_as_co.appendChild(me_as);

        let me_co = document.createElement('div');
        me_co.className = 'gentz_co';
        me_co.innerText = me_html;
        me_as_co.appendChild(me_co);

        if (this.left) {
            me_as.appendChild(this.left.html_print());
        }
        if (this.right) {
            let space = document.createElement('div');
            space.className = 'gentz_as_space';
            me_as.appendChild(space);
            me_as.appendChild(this.right.html_print());
        }

        return me;
    }
}

function frm_parse(str)
{
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(str.trim());
    let f = parser.results[0].form;

    let tr = fr => {
        fr.last_ts = 0;
        if (fr.e)
            tr(fr.e);
        if (fr.e1)
            tr(fr.e1);
        if (fr.e2)
            tr(fr.e2);
        return;
    }

    tr(f);

    return f;
}

function init_sequent(ante, succ)
{
    result = new sequent();
    result.ante = ante ? [ frm_parse(ante) ] : [];
    result.succ = [ frm_parse(succ) ];
    return result;
}

function s_terms(s /*sequent*/) /* tuple[rls: seq[string], vars: seq[string]] */
{
    let terms = s.ante.concat(s.succ).map(f => frm_terms(f)).flat();

    terms.sort((a, b) => a[0] == 'e' && b[0] == 'e' ?
        Number.parseInt(a.substring(1)) - Number.parseInt(b.substring(1)) :
        a.localeCompare(b)
    );
    return terms;
}


function axiom(s /*sequent*/) /*bool*/
{
    return s.ante.some(f => f.op == lfals) ||
        s.succ.some(f => f.op == ltrue) ||
        s.ante.some( f => s.succ.some( g => formulas_eql(f, g) ))
}

var seq_ts = -1;
function get_ts() {
    ++seq_ts;
    return seq_ts;
}

function inversion(s /* sequent */, todo /* [sequent] */, timeout = get_time()) /*bool*/
{
    if (!todo)
        todo = [];
    /* todo sluzi samo sljedecoj liniji */
    if (todo.length > timeout)
        throw "too long";
    if (axiom(s))
        return true;

    if (s.left != null || s.right != null)
        throw "inversion already performed";

    let left, right;
    let good = true;
    let best_formula = null;
    let best_formula_i = 0;
    let best_formula_pos = 0; /* -1 = ante, 1 = succ */

    let reg = (f, i, p) => {best_formula = f; best_formula_i = i; best_formula_pos = p;};

    for (let [i, f] of s.ante.entries())
    {
        switch (f.op) {
            case lfals: case ltrue: case lnot:
            case lcond: case land: case lor: case liff:
                reg(f, i, -1);
                break;
            case lall: case lexists:
                if (best_formula && ![lall, lexists].includes( best_formula.op ))
                    continue;
                if (!best_formula || f.last_ts < best_formula.last_ts ||
                    f.last_ts == best_formula.last_ts && f.op == lexists)
                    reg(f, i, -1);
        }
    }

    for (let [i, f] of s.succ.entries())
    {
        switch (f.op) {
            case lfals: case ltrue: case lnot:
            case lcond: case land: case lor: case liff:
                reg(f, i, 1);
                break;
            case lall: case lexists:
                if (best_formula && ![lall, lexists].includes( best_formula.op ))
                    continue;
                if (!best_formula || f.last_ts < best_formula.last_ts ||
                    f.last_ts == best_formula.last_ts && f.op == lall)
                    reg(f, i, 1);
        }
    }

    let f = best_formula;
    let i = best_formula_i;

    if (!f || !f.op)
        throw "too long"; // nothing to do...

    if (best_formula_pos == -1)
    {
        switch (f.op) {
            case lfals: case ltrue: case lnot:
            case land: case liff: case  lall: case lexists:
                left = new sequent();
                deep_copy(s, left);
                s.left = left;
                todo.push(left);
                break;
            case lor: case lcond:
                left = new sequent();
                deep_copy(s, left);
                right = new sequent();
                deep_copy(s, right);
                s.left = left;
                s.right = right;
                todo.push(left, right);
                break;
            default:
                /*throw "unknown operator " + f.op;*/
        }

        switch (f.op) {
            case lfals: case ltrue:
                break;
            case lnot:
                left.succ.push(f.e);
                break;
            case land:
                left.ante.push(f.e1);
                left.ante.push(f.e2);
                break;
            case liff:
                let k1 = deep_copy(f);
                k1.op = lcond;
                let k2 = deep_copy(k1);
                k2._e1 = k2.e1;
                k2.e1 = k2.e2;
                k2.e2 = k2._e1;
                left.ante.push(k1);
                left.ante.push(k2);
                break;
            case lor:
                left.ante.push(f.e1);
                right.ante.push(f.e2);
                break;
            case lcond:
                left.succ.push(f.e1);
                right.ante.push(f.e2);
                break;
            case lall: case lexists:
                f = left.ante[i]; /* let? */
                let q = f.v; /*quantified var*/
                let templat = f.e;
                let old_ts = f.last_ts;
                f.last_ts = get_ts();
                let terms = s_terms(s);
                let found = false;
                let sub = "";
                if (f.op == lall) {
                    for (let t of terms) {
                        if (!left.ante.some(inst => subst_inst_of(inst, f.e, { v: f.v,  c: t,  total: true, ignore_transl: false  }, false  ) )
                            && (!f.used_terms || !f.used_terms.includes(t) )
                        )
                        {

                            found = true; /*is this needed for this subst_inst_of?*/
                            sub = t;
                            break;
                        }
                    }
                }
                if (!found) {
                    let k = 0
                    while (terms.includes( "e_" + k.toString()))
                        ++k;
                    sub = "e_" + k.toString();
                }
                if (!f.used_terms)
                    f.used_terms = [];
                f.used_terms.push(sub);

                let inst = deep_copy(templat);
                subst(inst, q, sub);
                inst.last_ts = old_ts;
                left.ante.push(inst);
                break;
            default:
                /* throw "unknown operator " + f.op; */
        }
        if (left)
        {
            if (! [lall, lexists].includes(f.op))
                left.ante.splice(i, 1);
            good = good && inversion(left, todo);
        }
        if (right)
        {
            // if (! [lall, lexists].includes(f.op)) // ???
                right.ante.splice(i, 1);
            good = good && inversion(right, todo);
        }
        return good;
    }





    switch (f.op) {
        case lfals: case ltrue: case lnot:
        case lor: case lcond: case  lall: case lexists:
            left = new sequent();
            deep_copy(s, left);
            s.left = left;
            todo.push(left);
            break;
        case land: case liff:
            left = new sequent();
            deep_copy(s, left);
            right = new sequent();
            deep_copy(s, right);
            s.left = left;
            s.right = right;
            todo.push(left, right);
            break;
        default:
        /*throw "unknown operator " + f.op;*/
    }

    switch (f.op) {
        case lfals: case ltrue:
            break;
        case lnot:
            left.ante.push(f.e);
            break;
        case lor:
            left.succ.push(f.e1);
            left.succ.push(f.e2);
            break;
        case land:
            left.succ.push(f.e1);
            right.succ.push(f.e2);
            break;
        case liff:
            let k1 = deep_copy(f);
            k1.op = lcond;
            let k2 = deep_copy(k1);
            k2._e1 = k2.e1;
            k2.e1 = k2.e2;
            k2.e2 = k2._e1;

            left.succ.push(k1);
            right.succ.push(k2);
            break;
        case lcond:
            left.ante.push(f.e1);
            left.succ.push(f.e2);
            break;
        case lall: case lexists:
            f = left.succ[i]; /* let? */
            let q = f.v; /*quantified var*/
            let templat = f.e;
            let old_ts = f.last_ts;
            f.last_ts = get_ts();
            //let [rls, terms] = relationals(s);
            let terms =  s_terms(s);
            let found = false;
            let sub = "";
            if (f.op == lexists) {
                for (let t of terms) {
                    if (!left.succ.some(inst => subst_inst_of(inst, f.e, { v: f.v,  c: t,  total: true, ignore_transl: false  }, false  ) )
                        && (!f.used_terms || !f.used_terms.includes(t) )
                    )
                    {
                        found = true; /*is this needed for this subst_inst_of?*/
                        sub = t;
                        break;
                    }
                }
            }
            if (!found) {
                let k = 0
                while (terms.includes( "e_" + k.toString()))
                    ++k;
                sub = "e_" + k.toString();
            }
            if (!f.used_terms)
                f.used_terms = [];
            f.used_terms.push(sub);

            let inst = deep_copy(templat);
            subst(inst, q, sub);
            inst.last_ts = old_ts;
            left.succ.push(inst);
            break;
        default:
        /* throw "unknown operator " + f.op; */
    }
    if (left)
    {
        if (! [lall, lexists].includes(f.op))
            left.succ.splice(i, 1);
        good = good && inversion(left, todo);
    }
    if (right)
    {
        // if (! [lall, lexists].includes(f.op)) // ???
        right.succ.splice(i, 1);
        good = good && inversion(right, todo);
    }

    return good;

}
