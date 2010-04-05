
import java.util.Iterator;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
import java.util.NoSuchElementException;

/**
 *
 * @author victor
 */
public class ListaString implements Lista {
    
    private Nodo l;
    
    public ListaString () {
        l = null;
    }

    public void agregarh(Object e) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public void agregart(Object e) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public void agregar(int p, Object e) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public void eliminar(int p, Object e) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public Object get(int p) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public boolean isEmpty() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    public Iterator iterar() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    // CLASES INTERNAS:
    
    private static class Nodo {
        String elem;
        Nodo sig;
    }
    
    private static class IterLista implements Iterator {
        
        private Nodo n;
        
        public IterLista(Nodo a) {
            n = a;
        }

        public boolean hasNext() {
            return n.sig != null;
        }

        public Object next() {
            if (n.sig == null) {
                return new NoSuchElementException("Ya no hay mas elementos...");
            } else {
                Nodo aux = n;
                n = n.sig;
                return aux.elem;
            }
        }

        public void remove() {
            throw new UnsupportedOperationException("Not supported yet.");
        }
        
    }
}
