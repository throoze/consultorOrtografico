/**
 *
 * @author victor
 */
public class ExcepcionNoEsArchivo extends Exception {
    String mensaje;
    /**
     * Creates a new instance of <code>ExcepcionNoEsArchivo</code> without detail message.
     */
    public ExcepcionNoEsArchivo() {
        mensaje = "El nombre pasado no es un archivo...";
    }
    
    /**
     * Constructs an instance of <code>ExcepcionNoEsArchivo</code> with the specified detail message.
     * @param msg the detail message.
     */
    public ExcepcionNoEsArchivo(String msg) {
        super(msg);
        mensaje = msg;
    }
    
    public String gerMessage ()
    {
        return mensaje;
    }
}
