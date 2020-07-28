import React from 'react';

interface UrlFormProps {
  url: string;
  onSubmit: (value: string) => void;
  clearUrlParam: () => void;
}
interface UrlFormState {
  value: string;
}
export class UrlForm extends React.Component<UrlFormProps, UrlFormState> {
  constructor(props) {
    super(props);
    this.state = { value: this.props.url };

    this.handleChange = this.handleChange.bind(this);
    this.handleSubmit = this.handleSubmit.bind(this);
  }

  handleChange(event) {
    this.setState({ value: event.target.value });
    this.props.clearUrlParam();
  }

  handleSubmit(event) {
    this.props.onSubmit(this.state.value);
    event.preventDefault();
  }

  render() {
    return (
      <div className='urlForm'>
        <form onSubmit={this.handleSubmit}>
          <span className='url'>Load .lean from&nbsp;</span>
          URL:&nbsp;
          <input
            type='text'
            value={this.state.value}
            onChange={this.handleChange}
          />
          <input type='submit' value='Load' />
        </form>
      </div>
    );
  }
}
