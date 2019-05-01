var status_div = document.querySelector("#status"),
    in_div = document.querySelector("#in"),
    out_div = document.querySelector("#out"),
    out_sequent = document.querySelector("#out_sequent"),
    out_lat_div = document.querySelector("#out_lat"),
    out_dbg_div = document.querySelector("#out_dbg");



function compile() {
    try {
        let seq = in_div.value.trim().split('-->');

        let s = new sequent();
        s.ante = seq[0].split(',').filter(f => f.trim() != '').map(frm_parse);
        s.succ = seq[1].split(',').filter(f => f.trim() != '').map(frm_parse);

        window.s = s;

        inversion(s);


        while (out_sequent.firstChild)
            out_sequent.firstChild.remove()
        out_sequent.appendChild(s.html_print());

        out_lat_div.innerHTML = s.latex_print();
    } catch (e) {
        throw e;
    }

}

