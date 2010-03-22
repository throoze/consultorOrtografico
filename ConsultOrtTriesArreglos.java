import java.util.Iterator;
//@ model import org.jmlspecs.models.*;
import java.util.NoSuchElementException;
public class ConsultOrtTriesArreglos implements ConsultOrt {
    final static int TAMALFA = 26;
    private /*@ spec_public @*/ Nodo vt;
    
    private static class Nodo{
	
        public Nodo at[];
        public boolean esPalabra;
		
	    Nodo(){
                this.at = new Nodo[TAMALFA];
		this.esPalabra = false;
	    }
            
        /**
         * Operacion que devuelve un valor booleano que indica si el String que se 
         * le pasa es una palabra "bien formada", esto es, cada uno de los 
         * caracteres que lo conforman pertenece al conjunto { a - z } (alfabeto 
         * ingles).
         * @param p
         * @return valor booleano que indica si el String que se le pasa es una 
         *         palabra "bien formada", esto es, cada uno de los caracteres que 
         *         lo conforman pertenece al conjunto { a - z } (alfabeto ingles).
         */
        /*@ requires true;
          @ ensures \result <==> (!p.equals("")
          @             && 
          @             (\forall int e ; 0 <= e && e < p.length() 
          @                 ; 0 <= p.charAt(e) - 'a' 
          @                 &&
          @                 p.charAt(e) - 'a' <= 25
          @             )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ boolean wf (String p) {
            if (!p.equals("")) {
                boolean bf = true;
                /*@ loop_invariant 0 <= k && k <= p.length() &&
                  @         bf <==> (!p.equals("") &&
                  @                     (\forall int e; 0 <= e && e < k;
                  @                         0 <= p.charAt(e) - 'a'
                  @                         &&
                  @                         p.charAt(e) - 'a' <= 25 
                  @                     )
                  @                 );
                  @ decreasing p.length() - k;
                  @*/
                for (int k = 0; k < p.length() && bf; k++) {
                    int code = p.charAt(k) - 'a';
                    bf = (0 <= code && code <= 25);
                }
                return bf;
            
            } else {
                return false;
            }
        }
        
        /**
         * Operacion que devuelve un valor booleano que indica si el primer 
         * parametro pasado es prefijo del segundo parametro pasado (ambos de tipo 
         * String). 
         * @param p de tipo String, prefijo a consultar
         * @param q de tipo String, palabra sobre la cual se consultara el prefijo
         * @return Valos booleano que devuelve 'true' si 'p' es prefijo de 'q' y 
         *         devuelve 'false' en caso contrario.
         */    
        /*@ requires this.wf(p) && this.wf(q);
          @ ensures \result <==> p.length() <= q.length()
          @             &&
          @             (\forall int i ; 0 <= i && i < p.length() 
          @                 ; p.charAt(i) - q.charAt(i) == 0
          @             );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ boolean isPreFix (String p, String q) {
            boolean ipf = true;
            if (p.length() <= q.length()) {
                /*@ loop_invariant 0 <= k && k <= p.length() &&
                  @                (\forall int i; 0 <= i && i < k;
                  @                         p.charAt(i) - q.charAt(i) == 0
                  @                ) <==> ipf;
                  @ decreasing p.length() - k;
                  @*/
                for (int k = 0; k < p.length() && ipf ; k++) {
                    if (!(p.charAt(k) - q.charAt(k) == 0)) {
                        ipf = false;
                    }
                }
                return ipf;
            } else {
                return false;
            }
        }
        
        /*@ requires true;
          @ ensures (this == null && \result <==> true)
          @         ||
          @         (
          @             (this != null)
          @             &&
          @             (   
          @                 \result
          @                 ==
          @                 (
          @                     (\forall int e;
          @                             0 <= e && e < this.at.length;
          @                                                 this.at[e] == null
          @                     )
          @                     &&
          @                     this.esPalabra
          @                 )
          @             )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ boolean isEmpty() {
            if (this != null) {
                boolean nulo = true;
                /*@ loop_invariant 0 <= k && k <= this.at.length &&
                  @       (\forall int i; 0 <= i && i < 26; this.at[i] == null);
                  @ decreasing this.at.length - k;
                  @*/
                for (int k = 0; k < this.at.length && nulo; k++) {
                    if (this.at[k] != null) {
                        nulo = false;
                    }
                }
                if (nulo) {
                    nulo = !(this.esPalabra);
                }
                return nulo;
            } else {
                return true;
            }
        }
        
        /*@ requires true;
          @ ensures (!this.wf(p) && \result <==> false)
          @         ||
          @         (
          @             this.wf(p)
          @             &&
          @             \result 
          @             <==>
          @             (
          @                 !this.at[toInt(p,0)].isEmpty()
          @                 && 
          @                 (
          @                     (
          @                         (1 < p.length())
          @                         &&
          @                         this.at[toInt(p,0)].isIn(p.substring(1))
          @                     )
          @                     ||
          @                     (
          @                         (p.length() <= 1)
          @                         &&
          @                         this.esPalabra
          @                     )
          @                 )
          @             )
          @         );
          @ assignable \nothing;
          @ measured_by p.length();
          @*/ 
        public /*@ pure @*/ boolean isIn (String p) {
            if (!wf(p)) {
                return false;
            } else {
                boolean esta = true;
                Nodo t = this;
                /*@ loop_invariant 0 <= k && k <= p.length() &&
                  @         (*Se han revisado los nodos correspondientes a las letras de p hasta la k-esima*);
                  @ decreasing p.length() - k;
                  @*/
                for(int k = 0; k < p.length() && esta; k++){
                    int i = p.charAt(k) - 'a';
                    if (t.at[i] == null) {
                        esta = false;
                    } else {
                        t = t.at[i];
                        if (k == p.length() - 1 && t.esPalabra) {
                            esta = true;
                        } else if (k == p.length() - 1 && !t.esPalabra) {
                            esta = false;
                        }
                    }
                }
                return esta;
            }
        }
        
        /*@ requires 0 <= i && i < 26;
          @ ensures 10 <= Character.getNumericValue(\result);
          @ ensures Character.getNumericValue(\result) <= 35;
          @ ensures 0 <= \result - 'a' && \result - 'a' <= 25;
          @ ensures \result - 'a' == i;
          @ assignable \nothing;
          @*/
        public static /*@ pure @*/ char toChar(int i){
            char[] a = {'a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z'};
            return a[i];
        }
        
        /*@ requires !p.equals("");
          @ requires (\forall int e ;
          @                     0 <= e && e < p.length();
          @                                 0 <= p.charAt(e) - 'a' 
          @                                 &&
          @                                 p.charAt(e) - 'a' < 26
          @          );
          @ requires 0 <= n && n < p.length();
          @ ensures \result == (p.charAt(n) - 'a');
          @ ensures 0 <= \result && \result < 26;
          @ assignable \nothing;
          @*/
        public static /*@ pure @*/ int toInt (String p, int n) {
            return (p.charAt(n) - 'a');
        }
        
        /*@ requires true;
          @ ensures (this == null && \result == 0)
          @         ||
          @         (this != null
          @         &&
          @         \result 
          @         ==
          @         (this.esPalabra ? 1 : 0) + (\sum int i;
          @                                         0 <= i && i < 26;
          @                                             this.at[i].countWords()
          @                                     )
          @         );
          @ assignable \nothing;
          @*/
        public /*@ pure @*/ int countWords () {
            int n = 0;
            if (this != null) {
                /*@ loop_invariant 0 <= k && k <= 26 &&
                  @    n == (\sum int i;
                  @                 0 <= i && i < k;
                  @                         this.at[i].countWords()
                  @         );
                  @ decreasing 26 - k;
                  @*/
                for (int k = 0; k < 26; k++) {
                    if (this.at[k] != null) {
                        n = n + this.at[k].countWords();
                    }
                }
                return (n + (this.esPalabra ? 1 : 0));
            } else {
                return 0;
            }
        }
        
        
        /*@ requires true;
          @ ensures (\forall int i;
          @             0 <= i && i < \result.length;
          @                 this.isIn(\result[i])
          @         )
          @         && (*Si una palabra esta en this, esta tambien en \result*);
          @*/
        public /*@ pure @*/ String[] extractWordsA () {
            String[] words = new String[this.countWords()];
            int i = 0;
            if (this.esPalabra) {
                words[i] = "";
                i = 1;
            }
            if (this != null) {
                /*@ loop_invariant  0 <= k && k <= 26 &&
                  @     (*Se han extraido las palabras de los hijos de this 
                  @       hasta el k-esimo hijo, y se han almacenado en el 
                  @       arreglo de salida, cada palabra concatenada al 
                  @      principio con el caracter correspondiente a si mismo*);
                  @ decreasing 26 -k;
                  @*/
                for (int k = 0; k < 26; k++) {
                    if (this.at[k] != null) {
                        String[] tmp = this.at[k].extractWordsA();
                        /*@ loop_invariant 0 <= c && c <= tmp.length &&
                          @     (\forall int n,m; 0 <= n && n < c &&
                          @                     i-c <= m && m < i ;
                          @         words[m].equals
                          @             (Character.toString(toChar(k)) + tmp[n])
                          @     );
                          @ decreasing tmp.length - c;
                          @*/
                        for (int c = 0; c < tmp.length; c++) {
                            words[i] = Character.toString(toChar(k)) + tmp[c];
                            i++;
                        }
                    }
                }
            }
            return words;
        }
    }

    private static class elGenTries implements Iterator {
        
        private /*@ spec_public @*/ String[] seq;
        private /*@ spec_public @*/ int index;
        
        //@ public represents moreElements <- this.hasNext();
        
        /*@ requires true;
          @ ensures this.seq.length == n.countWords();
          @ ensures (\forall int i; 
          @                 0 <= i && i < this.seq.length;
          @                         n.isIn(this.seq[i])
          @         );
          @ ensures this.index == 0;
          @*/
        public elGenTries (Nodo n) {
            this.seq = n.extractWordsA();
            //this.seq = new String[tmp.length];
            /*
            for (int k = 0; k < tmp.length; k++) {
                this.seq[k] = tmp[k];
            }
             */
            this.index = 0;
        }
        
        /*@ also
          @ requires true;
          @ ensures \result <==> (this.index < this.seq.length);
          @*/
        public /*@ pure @*/ boolean hasNext () {
            return (this.index < this.seq.length);
        }
        
        /*@ also
          @ public normal_behavior
          @ requires this.hasNext();
          @ ensures this.index == \old(this.index) + 1;
          @ ensures \result == this.seq[\old(this.index)];
          @ assignable this.index;
          @
          @ also
          @ public exceptional_behavior
          @ requires !this.hasNext();
          @ signals_only NoSuchElementException;
          @ signals (NoSuchElementException) !this.hasNext();
          @ assignable \nothing;
          @*/ 
        public Object next () throws NoSuchElementException {
            if (this.hasNext()){
                this.index++;
                return this.seq[this.index - 1];
            } else {
                return new NoSuchElementException("Ya no hay mas elementos...");
            }
        }
        
        /*@ also
          @ requires true;
          @ ensures true;
          @ assignable \nothing;
          @*/ 
        public void remove() {
            System.out.println("Operacion no implementada para este tipo...");
        }
        
    }
    
    // public invariant ok(vt);
	
    /*@ requires t.isEmpty();
      @ ensures \result <==> true;
      @ also
      @ requires !t.isEmpty();
      @ ensures \result
      @         <==>
      @         (
      @             (\forall int e;
      @                     0 <= e && e < 26;
      @                             (t.at[e].isEmpty())==>t.esPalabra
      @             )
      @             &&
      @             (\forall int e;
      @                     0 <= e && e < 26;
      @                             ok(t.at[e])
      @             )
      @         );
      @ public pure model boolean ok(Nodo t){
      @     if (t.isEmpty()) {
      @         return true;
      @     } else {
      @         boolean flag = true;
      @         for (int k = 0 ; k < 26 && flag; k++) {
      @             if (!((t.at[k].isEmpty() ==> t.esPalabra) && ok(t.at[k]))) {
      @                 flag = false;
      @             }
      @         }
      @         return flag;
      @     }
      @ }
      @*/
	
    /*@ public represents
      @     vocabulario <- extr(this.vt);
      @*/
	  
    /*@ public pure model JMLValueSet extr(Nodo t){
      @     JMLValueSet tmp = extr("", t);
      @     return tmp;
      @ }     
      @  
      @ private pure model JMLValueSet extr(String s, Nodo t){
      @     JMLValueSet tmp = new JMLValueSet();
      @     if (t != null)
      @         if (t.esPalabra)
      @             tmp = tmp.union(new JMLValueSet(new JMLString(s)));
      @         for (int i = 0; i < TAMALFA; i++)
      @             if(t.at[i] != null)
      @                tmp = tmp.union(extr(s + (char)(i + 'a'), t.at[i]));    	
      @     return tmp;
      @ }      
      @*/
	
    /*@ requires
            true;
      @ ensures
            vt != null;
      @*/
    public ConsultOrtTriesArreglos()
    {
        vt = new Nodo();
    }
	
    /*@ also 
      @ public normal_behavior
      @ requires bf(p) && !this.vt.isIn(p);
      @ ensures this.vt.isIn(p) && 
      @     (*Se conservan el resto de las palabras que pertenecian al arbol*);
      @ assignable vt;
      @ also 
      @ public exceptional_behavior
      @ requires !bf(p)
      @          ||
      @          this.vt.isIn(p);
      @ signals_only ExcepcionPalabraNoBienFormada,
      @              ExcepcionPalabraYaRegistrada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(p);
      @ signals (ExcepcionPalabraYaRegistrada) this.vt.isIn(p);
      @ assignable \nothing;
      @*/
    public void agregar(String p) throws
	    ExcepcionPalabraNoBienFormada, 
	    ExcepcionPalabraYaRegistrada
    {
        if (!bf(p)) {
            throw new ExcepcionPalabraNoBienFormada
                    ("La palabra \""+p+"\" esta mal formada...");
        } else {
            Nodo t = vt;
            /*@ loop_invariant 0 <= k && k <= p.length() && 
              @     (*Si hace falta, se han inicializado todos los nodos 
              @       correspondientes a las letras de p hasta la k-esima 
              @       letra*);
              @ decreasing p.length() - k;
              @*/
	    for(int k = 0; k < p.length(); k++){
                int i = p.charAt(k) - 'a';
	        if (t.at[i] == null) {
	            t.at[i] = new Nodo();
                    t = t.at[i];
                } else {
                    t = t.at[i];
		    if (k == p.length() - 1 && t.esPalabra) {
		        throw new ExcepcionPalabraYaRegistrada
                                 ("La palabra \""+p+"\" ya esta registrada...");
                    }
                }
	    }
	    t.esPalabra = true;
        }
    }
	
    /*@ also
      @ requires true;
      @ ensures \result <==> (!p.equals("")
      @             && 
      @             (\forall int e ; 0 <= e && e < p.length() 
      @                 ; 0 <= p.charAt(e) - 'a' 
      @                 &&
      @                 p.charAt(e) - 'a' <= 25
      @             )
      @         );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean  bf(String p)
    {
	return vt.wf(p);
    }
	
    /*@ also
      @ requires bf(p) && bf(q);
      @ ensures \result <==> p.length() <= q.length()
      @             &&
      @             (\forall int i ; 0 <= i && i < p.length() 
      @                 ; p.charAt(i) - q.charAt(i) == 0
      @             );
      @ assignable \nothing;
      @*/
    public /*@ pure @*/ boolean  ipf(String p, String q)
    {
	return this.vt.isPreFix(p, q);
    }

    /*@ also 
      @ public normal_behavior
      @ requires this.bf(pr);
      @ ensures (*El arbol no se ha modificado*);
      @ ensures (\forall int i, j ;
      @                     0 <= i && i < \result.length
      @                     &&
      @                     0 <= j && j < \result.length
      @                     &&
      @                     i != j;
      @                                 !\result[i].equals(\result[j])
      @         );
      @ ensures (\forall int i ;
      @                 0 <= i && i < \result.length;
      @                         this.vt.isIn(\result[i])
      @         );
      @ ensures (\forall int i ;
      @                     0 <= i && i < \result.length;
      @                                 ipf(pr, \result[i])
      @         );
      @ ensures (\forall int i;
      @             0 <= i && i < \result.length && 
      @             !this.vt.isIn(\result[i]);
      @             !ipf(pr,\result[i])
      @         );
      @ assignable \nothing;
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pr);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pr);
      @ assignable \nothing;
      @*/
    public String[] consultarPorPrefijo(String pr) throws 
        ExcepcionPalabraNoBienFormada
    {
        if (!bf(pr)) {
            throw new ExcepcionPalabraNoBienFormada
                    ("La palabra \""+pr+"\" esta mal formada...");
        } else {
            Nodo t = vt;
            String[] palabras = new String[0];
            boolean stop = false;
            /*@ loop_invariant 0 <= k && k <= pr.length() &&
              @     (*Se ha bajado por el arbol hasta el nodo que rrepresenta la
              @       k-esima letra de pr*);
              @ decreasing pr.length() - k;
              @*/
	    for(int k = 0; k < pr.length() && !stop; k++){
                int i = pr.charAt(k) - 'a';
	        if (t.at[i] == null) {
	            stop = true;
                    return palabras;
                }
                t = t.at[i];
	    }
            if (t != null) {
                String[] tmp = t.extractWordsA();
                palabras = new String[tmp.length];
                /*@ loop_invariant 0 <= k && k <= tmp.length &&
                  @     (\forall int i;
                  @             0 <= i && i < k;
                  @                     palabras[i].equals(pr + tmp[i])
                  @     );
                  @ decreasing tmp.length - k;
                  @*/
                for (int k = 0; k < tmp.length; k++) {
                    palabras[k] = pr + tmp[k];
                }
            }
            return palabras;
        }
    }	

    /*@ also 
      @ public normal_behavior
      @ requires this.bf(pl);
      @ ensures true;
      @ assignable \nothing;
      @ also 
      @ public exceptional_behavior
      @ requires !bf(pl);
      @ signals_only ExcepcionPalabraNoBienFormada;
      @ signals (ExcepcionPalabraNoBienFormada) !bf(pl);
      @ assignable \nothing;
      @*/
    public String prefijoMasLargo(String pl) throws 
        ExcepcionPalabraNoBienFormada
    {
        if (!bf(pl)) {
            throw new ExcepcionPalabraNoBienFormada
                    ("La palabra \""+pl+"\" esta mal formada...");
        } else {
            String pml = "";
            Nodo t = vt;
            boolean stop = false;
            /*@ loop_invariant 0 <= k && k <= pl.length();
              @ decreasing pl.length() - k;
              @*/
	    for(int k = 0; k < pl.length() && !stop; k++){
                int i = pl.charAt(k) - 'a';
                pml = pl.substring(0, k+1);
	        if (t.at[i] == null) {
                    pml = pl.substring(0, k);
	            stop = true;
                }
                t = t.at[i];
	    }
            return pml;
        }
    }
    
    /*@ also
      @ requires true;
      @ ensures \result != null;
      @*/
    public Iterator elems() {
        return new elGenTries(this.vt);
    }
}